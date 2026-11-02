/* jitdump.inc: tell profilers where Scheme code is, as it is created and
 * as the collector moves it.
 *
 * CHEZ_JITDUMP=DIR writes DIR/jit-PID.dump in the jitdump format that
 * `perf inject --jit` reads (record with `perf record -k mono`). The
 * file is opened before the boot files load; it gets every code object in
 * the heap once they are loaded, and a load record for code as it is created (written
 * before the next collection, once the code is filled in, but stamped
 * with the time it was created). When the collector moves code that has a
 * record, the code gets a move record (old and new address, no code bytes),
 * which `perf inject` turns into a mapping of the original record's code
 * at the new address; moved code without a known record gets a new load
 * record. So an address is named by whichever code was there when a
 * sample was taken.
 *
 * Move records are enough to name samples, but a move record maps the
 * code bytes as they were first recorded, while the collector rewrites
 * the code's direct calls and jumps to other code (rel32 on x86_64) as it
 * moves it, so tools that decode instructions (Intel PT) need the real
 * bytes. CHEZ_JITDUMP_NO_MOVES=1 writes a full load record for moved
 * code instead. That makes the dump several times larger and slower to
 * write; it is also the way to use perf 7.0, whose `perf inject --jit`
 * crashes on move records (its JIT_CODE_MOVE path calls
 * build_id__mark_dso_hit with a NULL evsel).
 *
 * With CHEZ_JITDUMP_TSC=1 as well (x86_64 only), records carry TSC
 * timestamps and the header sets JITDUMP_FLAGS_ARCH_TIMESTAMP. perf cannot
 * use `-k mono` with Intel PT, so this is the way to name Scheme code in
 * a `perf record -e intel_pt//u` trace.
 *
 * Event-driven Intel PT snapshots (magic-trace): magic-trace snapshots
 * its trace buffer, which then holds the last few milliseconds, whenever
 * the program calls magic_trace_stop_indicator(start_tsc, arg), an empty
 * function it finds by name in the executable it runs (so run the scheme
 * or racket executable directly, with `magic-trace run -trigger .`), and
 * marks the stretch since start_tsc. Scheme
 * calls it through (foreign-procedure "(cs)magic_trace_snapshot"
 * (unsigned-64 unsigned-64) void), with a start from
 * (foreign-procedure "(cs)magic_trace_tsc" () unsigned-64).
 * CHEZ_MAGIC_TRACE_GC_MS=N also calls it after any collection that took
 * at least N ms, marking the collection, and CHEZ_MAGIC_TRACE_RENDEZVOUS_MS=N
 * calls it (arg 1) when a collection starts at least N ms after it was
 * requested, which is the time every thread takes to reach a safe point
 * (an event check with interrupts enabled); the per-CPU trace buffers
 * then show what the last threads to arrive were doing;
 * CHEZ_MAGIC_TRACE_RENDEZVOUS_SKIP=K skips the first K such collections
 * (every process waits a few ms at its first, during boot). magic-trace
 * only sees the call on the main thread, so another thread signals the
 * main thread (SIGRTMIN+6) to make it, and waits up to 50 ms.
 * CHEZ_GC_RENDEZVOUS_LOG=1 prints each collection's wait to stderr. With
 * CHEZ_JITDUMP_LAZY=1, the jitdump records nothing as the program runs;
 * instead, the first snapshot (every snapshot, with CHEZ_JITDUMP_LAZY=all,
 * for magic-trace -multi-snapshot) writes a load record for all live
 * code (after
 * a pause, CHEZ_MAGIC_TRACE_DELAY_MS, default 100, so that the walk does
 * not overwrite the buffer before magic-trace has saved it), stamped
 * with the time of the previous snapshot or of opening the file. That
 * names code correctly in a snapshot window unless a collection moved
 * code inside the window, and costs nothing until a snapshot.
 *
 * CHEZ_PERF_MAP=1 writes /tmp/perf-PID.map at exit, naming code where it
 * is at that point (perf report reads it without any extra steps).
 *
 * Linux on x86_64 and arm64 only, like the sampler.
 */

#if defined(__linux__) && (defined(__x86_64__) || defined(__aarch64__)) && defined(PTHREADS)

#include <time.h>
#include <sys/mman.h>
#include <sys/syscall.h>
#include <unistd.h>
#include <fcntl.h>
#include <signal.h>

#if defined(__x86_64__)
# define JITDUMP_ELF_MACH 62
#elif defined(__aarch64__)
# define JITDUMP_ELF_MACH 183
#elif defined(__i386__)
# define JITDUMP_ELF_MACH 3
#else
# define JITDUMP_ELF_MACH 0
#endif

static FILE *jitdump_f;
static void *jitdump_marker;
static U64 jitdump_index;
static pid_t jitdump_pid;
static s_thread_mutex_t jitdump_mutex;
static IBOOL jitdump_ready;    /* the file is open */
static IBOOL jitdump_tracking; /* recording code as it is created and moved (not lazy) */
static IBOOL jitdump_lazy_every, jitdump_lazy_done; /* lazy: dump at every snapshot; dumped once */
static ptr *jitdump_pending; static U64 *jitdump_pending_t; static uptr jitdump_npending, jitdump_maxpending;

/* code moved by the current collection. Sweeper threads add to it in
   parallel, so it is a list of chunks indexed by an atomic counter; only
   adding a chunk takes the lock. */
#define JITDUMP_CHUNK_BITS 14
#define JITDUMP_CHUNK (1 << JITDUMP_CHUNK_BITS)
#define JITDUMP_MAX_CHUNKS 16384
typedef struct { uptr old_entry; ptr co; I64 idx; } jitdump_move;
static jitdump_move *jitdump_chunks[JITDUMP_MAX_CHUNKS];
static uptr jitdump_nmoved;

/* the index of the load record whose code bytes are at each entry address,
   for move records; open addressing, keyed by entry address */
static uptr *jitdump_tab_key; static U64 *jitdump_tab_idx; static uptr *jitdump_tab_len;
static uptr jitdump_tab_size, jitdump_tab_count;

#if defined(__x86_64__)
# include <x86intrin.h>
#endif
static IBOOL jitdump_tsc;
static IBOOL jitdump_moves = 1;

static U64 jitdump_now(void) {
  struct timespec ts;
#if defined(__x86_64__)
  if (jitdump_tsc) return __rdtsc();
#endif
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (U64)ts.tv_sec * 1000000000ULL + (U64)ts.tv_nsec;
}

/* the code object's name, as perf should show it: the same text the sampler
   uses (name or [anonymous], then @file:line), without its _[i]/_[j] marks,
   so that PT stacks and sampled stacks line up */
static int jitdump_name(ptr co, char *buf, int max) {
  ptr name = CODENAME(co);
  iptr n, i, start; int len = 0;
  if (max > SAMPLER_NAME_MAX) max = SAMPLER_NAME_MAX;
  if (Sstringp(name)) {
    n = Sstring_length(name);
    start = n > max - 1 ? n - (max - 1) : 0;
    for (i = start; i < n; i++) {
      string_char c = Sstring_ref(name, i);
      buf[len++] = (c == ';' || c == ' ' || c < 32 || c > 126) ? '_' : (char)c;
    }
  }
  if (len == 0) { memcpy(buf, "[anonymous]", 11); len = 11; }
  if (sampler_srcloc && (buf[0] != '[' || name == Sfalse)) len = sampler_source_label(co, buf, len, max - 5);
  buf[len] = 0;
  return len;
}

static uptr jitdump_hash(uptr a) { return (a >> 4) * (uptr)0x9E3779B97F4A7C15ULL; }

static uptr jitdump_tab_slot(uptr key) {
  uptr mask = jitdump_tab_size - 1, i = jitdump_hash(key) & mask;
  while (jitdump_tab_key[i] != 0 && jitdump_tab_key[i] != key) i = (i + 1) & mask;
  return i;
}

static void jitdump_tab_put(uptr key, U64 idx, uptr len) {
  uptr i;
  if ((jitdump_tab_count + 1) * 2 > jitdump_tab_size) {
    uptr old_size = jitdump_tab_size, j, n = old_size ? old_size * 2 : 65536;
    uptr *ok = jitdump_tab_key, *ol = jitdump_tab_len; U64 *oi = jitdump_tab_idx;
    uptr *nk = calloc(n, sizeof(uptr)), *nl = malloc(n * sizeof(uptr)); U64 *ni = malloc(n * sizeof(U64));
    if (nk == NULL || ni == NULL || nl == NULL) { free(nk); free(ni); free(nl); return; }
    jitdump_tab_key = nk; jitdump_tab_idx = ni; jitdump_tab_len = nl; jitdump_tab_size = n; jitdump_tab_count = 0;
    for (j = 0; j < old_size; j++)
      if (ok[j] != 0) {
        i = jitdump_tab_slot(ok[j]);
        jitdump_tab_key[i] = ok[j]; jitdump_tab_idx[i] = oi[j]; jitdump_tab_len[i] = ol[j];
        jitdump_tab_count++;
      }
    free(ok); free(oi); free(ol);
  }
  i = jitdump_tab_slot(key);
  if (jitdump_tab_key[i] == 0) { jitdump_tab_key[i] = key; jitdump_tab_count++; }
  jitdump_tab_idx[i] = idx;
  jitdump_tab_len[i] = len;
}

/* remove key, returning its index and code length, or -1 if it is not there */
static I64 jitdump_tab_take(uptr key, uptr *len) {
  uptr i, j, mask; I64 idx;
  if (jitdump_tab_size == 0) return -1;
  i = jitdump_tab_slot(key);
  if (jitdump_tab_key[i] == 0) return -1;
  idx = (I64)jitdump_tab_idx[i];
  *len = jitdump_tab_len[i];
  /* backward-shift deletion, which keeps every other key reachable */
  mask = jitdump_tab_size - 1;
  jitdump_tab_key[i] = 0; jitdump_tab_count--;
  for (j = (i + 1) & mask; jitdump_tab_key[j] != 0; j = (j + 1) & mask) {
    uptr h = jitdump_hash(jitdump_tab_key[j]) & mask;
    /* move j's key into the hole at i unless its home h lies cyclically in (i, j] */
    if (i <= j ? (h <= i || h > j) : (h <= i && h > j)) {
      jitdump_tab_key[i] = jitdump_tab_key[j]; jitdump_tab_idx[i] = jitdump_tab_idx[j];
      jitdump_tab_len[i] = jitdump_tab_len[j];
      jitdump_tab_key[j] = 0; i = j;
    }
  }
  return idx;
}

static void jitdump_emit(ptr co, U64 when) {
  struct { U32 id, total_size; U64 timestamp; U32 pid, tid; U64 vma, code_addr, code_size, code_index; } rec;
  char name[1024];
  int nlen = jitdump_name(co, name, sizeof(name));
  uptr len = CODELEN(co);
  rec.id = 0; /* JIT_CODE_LOAD */
  rec.total_size = (U32)(sizeof(rec) + nlen + 1 + len);
  rec.timestamp = when;
  rec.pid = (U32)jitdump_pid;
  rec.tid = (U32)syscall(SYS_gettid);
  rec.vma = rec.code_addr = (U64)(uptr)CODEENTRYPOINT(co);
  rec.code_size = len;
  rec.code_index = jitdump_index++;
  jitdump_tab_put((uptr)rec.code_addr, rec.code_index, len);
  fwrite(&rec, sizeof(rec), 1, jitdump_f);
  fwrite(name, nlen + 1, 1, jitdump_f);
  fwrite(TO_VOIDP(CODEENTRYPOINT(co)), len, 1, jitdump_f);
}

static void jitdump_push(ptr **v, uptr *n, uptr *max, ptr co) {
  if (*n == *max) {
    uptr m = *max ? *max * 2 : 4096;
    ptr *nv = realloc(*v, m * sizeof(ptr));
    if (nv == NULL) return;
    *v = nv; *max = m;
  }
  (*v)[(*n)++] = co;
}

static double magic_trace_ms(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return ts.tv_sec * 1e3 + ts.tv_nsec / 1e6;
}
static double magic_trace_gc_ms, magic_trace_gc_start;
static U64 magic_trace_gc_tsc;
static U64 s_magic_trace_tsc(void) {
#if defined(__x86_64__)
  return __rdtsc();
#else
  return 0;
#endif
}
/* time to safe point: from a collect request to the collection's start,
   which waits for every thread to reach an event check with interrupts on */
static double magic_trace_rdv_ms, magic_trace_rdv_req; static IBOOL magic_trace_rdv_log;
static U64 magic_trace_rdv_tsc; static long magic_trace_rdv_skip;
static void jitdump_collect_requested(void) {
  if (magic_trace_rdv_ms > 0 || magic_trace_rdv_log) {
    magic_trace_rdv_req = magic_trace_ms();
    magic_trace_rdv_tsc = s_magic_trace_tsc();
  }
}
static void s_magic_trace_snapshot(U64 start_tsc, U64 arg);

/* a code object just allocated; it gets its record once it is filled in */
void S_jitdump_code_created(ptr co) {
  if (!jitdump_tracking) return;
  s_thread_mutex_lock(&jitdump_mutex);
  /* forget code that used to be at this address: it is dead, and the new
     code must not be mistaken for it if it moves before it has a record */
  { uptr len; (void)jitdump_tab_take((uptr)CODEENTRYPOINT(co), &len); }
  if (jitdump_npending == jitdump_maxpending) {
    U64 *nt = realloc(jitdump_pending_t, (jitdump_maxpending ? jitdump_maxpending * 2 : 4096) * sizeof(U64));
    if (nt != NULL) jitdump_pending_t = nt;
  }
  if (jitdump_pending_t != NULL) {
    uptr i = jitdump_npending;
    jitdump_push(&jitdump_pending, &jitdump_npending, &jitdump_maxpending, co);
    /* the record carries the creation time, since the code runs from then on */
    if (jitdump_npending > i) jitdump_pending_t[i] = jitdump_now();
  }
  s_thread_mutex_unlock(&jitdump_mutex);
}

/* a code object that the collector has just swept into a new place;
   oldco is where it was, or 0 if the collector no longer knows */
void S_jitdump_code_moved(ptr oldco, ptr co) {
  uptr i, c; jitdump_move *chunk;
  if (!jitdump_tracking || oldco == co) return;
  i = __atomic_fetch_add(&jitdump_nmoved, 1, __ATOMIC_RELAXED);
  c = i >> JITDUMP_CHUNK_BITS;
  if (c >= JITDUMP_MAX_CHUNKS) return;
  chunk = __atomic_load_n(&jitdump_chunks[c], __ATOMIC_ACQUIRE);
  if (chunk == NULL) {
    s_thread_mutex_lock(&jitdump_mutex);
    chunk = jitdump_chunks[c];
    if (chunk == NULL) {
      chunk = malloc(JITDUMP_CHUNK * sizeof(jitdump_move));
      __atomic_store_n(&jitdump_chunks[c], chunk, __ATOMIC_RELEASE);
    }
    s_thread_mutex_unlock(&jitdump_mutex);
    if (chunk == NULL) return;
  }
  chunk += i & (JITDUMP_CHUNK - 1);
  chunk->old_entry = oldco == (ptr)0 ? 0 : (uptr)CODEENTRYPOINT(oldco);
  chunk->co = co;
}

static void jitdump_emit_move(uptr old_entry, ptr co, U64 idx, U64 when) {
  struct { U32 id, total_size; U64 timestamp; U32 pid, tid; U64 vma, old_code_addr, new_code_addr, code_size, code_index; } rec;
  rec.id = 1; /* JIT_CODE_MOVE */
  rec.total_size = (U32)sizeof(rec);
  rec.timestamp = when;
  rec.pid = (U32)jitdump_pid;
  rec.tid = (U32)syscall(SYS_gettid);
  rec.old_code_addr = old_entry;
  rec.vma = rec.new_code_addr = (U64)(uptr)CODEENTRYPOINT(co);
  rec.code_size = CODELEN(co);
  rec.code_index = idx;
  fwrite(&rec, sizeof(rec), 1, jitdump_f);
}

static IBOOL jitdump_codep(ptr co);

/* before a collection, record code created since the last one (now filled
   in; during boot, some is still a placeholder, which the check skips) */
void S_jitdump_before_gc(void) {
  uptr i;
  if (magic_trace_gc_ms > 0) { magic_trace_gc_start = magic_trace_ms(); magic_trace_gc_tsc = s_magic_trace_tsc(); }
  if (magic_trace_rdv_req > 0) {
    double w = magic_trace_ms() - magic_trace_rdv_req;
    magic_trace_rdv_req = 0;
    if (magic_trace_rdv_log) fprintf(stderr, "gc-rendezvous %.3f ms\n", w);
    if (magic_trace_rdv_ms > 0 && w >= magic_trace_rdv_ms && magic_trace_rdv_skip-- <= 0) s_magic_trace_snapshot(magic_trace_rdv_tsc, 1);
  }
  if (!jitdump_tracking) return;
  s_thread_mutex_lock(&jitdump_mutex);
  for (i = 0; i < jitdump_npending; i++)
    if (jitdump_codep(jitdump_pending[i])) jitdump_emit(jitdump_pending[i], jitdump_pending_t[i]);
  jitdump_npending = 0;
  jitdump_nmoved = 0;
  s_thread_mutex_unlock(&jitdump_mutex);
}

/* after a collection, record where it put the code it moved: a move
   record for code whose bytes the dump already has, a load record for the
   rest. Every old address leaves the table before any new one goes in,
   since one object's new address can be another's old one. */
void S_jitdump_after_gc(void) {
  uptr i, n; U64 t; jitdump_move *m;
  if (magic_trace_gc_ms > 0 && magic_trace_ms() - magic_trace_gc_start >= magic_trace_gc_ms)
    s_magic_trace_snapshot(magic_trace_gc_tsc, 0);
  if (!jitdump_tracking) return;
  s_thread_mutex_lock(&jitdump_mutex);
  t = jitdump_now();
  n = jitdump_nmoved;
  if (n > (uptr)JITDUMP_MAX_CHUNKS << JITDUMP_CHUNK_BITS) n = (uptr)JITDUMP_MAX_CHUNKS << JITDUMP_CHUNK_BITS;
  for (i = 0; i < n; i++) {
    if (jitdump_chunks[i >> JITDUMP_CHUNK_BITS] == NULL) continue;
    m = &jitdump_chunks[i >> JITDUMP_CHUNK_BITS][i & (JITDUMP_CHUNK - 1)];
    m->idx = -1;
    if (m->old_entry != 0) {
      uptr len; I64 idx = jitdump_tab_take(m->old_entry, &len);
      /* a different length means the record was for other code, which died */
      if (idx >= 0 && len == (uptr)CODELEN(m->co)) m->idx = idx;
    }
  }
  for (i = 0; i < n; i++) {
    seginfo *si;
    if (jitdump_chunks[i >> JITDUMP_CHUNK_BITS] == NULL) continue;
    m = &jitdump_chunks[i >> JITDUMP_CHUNK_BITS][i & (JITDUMP_CHUNK - 1)];
    si = MaybeSegInfo(ptr_get_segment(m->co));
    if (si == NULL || si->space != space_code || si->use_marks) continue;
    if (m->idx >= 0 && jitdump_moves) {
      jitdump_emit_move(m->old_entry, m->co, (U64)m->idx, t);
      jitdump_tab_put((uptr)CODEENTRYPOINT(m->co), (U64)m->idx, CODELEN(m->co));
    } else
      jitdump_emit(m->co, t);
  }
  jitdump_nmoved = 0;
  fflush(jitdump_f);
  s_thread_mutex_unlock(&jitdump_mutex);
}

/* ---------------------------------------------------------------------- */
/* walking all code in the heap */

static IBOOL jitdump_codep(ptr co) {
  iptr len, nfree; ptr name;
  seginfo *si = MaybeSegInfo(ptr_get_segment(co));
  if (si == NULL || si->space != space_code) return 0;
  if ((CODETYPE(co) & mask_code) != type_code) return 0;
  len = CODELEN(co); nfree = CODEFREE(co);
  if (len < 0 || len > ((iptr)1 << 28) || nfree < 0 || nfree > ((iptr)1 << 20)) return 0;
  name = CODENAME(co);
  if (name != Sfalse && !(((uptr)name & mask_typed_object) == type_typed_object
                          && MaybeSegInfo(ptr_get_segment(name)) != NULL && Sstringp(name)))
    return 0;
  return 1;
}

static int jitdump_seg_cmp(const void *a, const void *b) {
  uptr x = *(const uptr *)a, y = *(const uptr *)b;
  return x < y ? -1 : x > y;
}

/* call f on each code object in the heap, in address order */
static void jitdump_each_code(void (*f)(ptr co, void *arg), void *arg) {
  uptr *segs = NULL, nsegs = 0, max = 0, i, skip_to = 0;
  IGEN g;
  for (g = 0; g <= static_generation; g++) {
    seginfo *si;
    if (g > S_G.max_nonstatic_generation && g != static_generation) continue;
    for (si = S_G.occupied_segments[g][space_code]; si != NULL; si = si->next) {
      if (nsegs == max) { max = max ? max * 2 : 1024; segs = realloc(segs, max * sizeof(uptr)); if (!segs) return; }
      segs[nsegs++] = si->number;
    }
  }
  qsort(segs, nsegs, sizeof(uptr), jitdump_seg_cmp);
  for (i = 0; i < nsegs; i++) {
    uptr a = (uptr)build_ptr(segs[i], 0), end = a + bytes_per_segment;
    if (skip_to > a) a = skip_to;
    a = (a + byte_alignment - 1) & ~(uptr)(byte_alignment - 1);
    while (a < end) {
      ptr co = TYPE((ptr)a, type_typed_object);
      if (jitdump_codep(co)) {
        f(co, arg);
        a += size_code(CODELEN(co));
        skip_to = a;
      } else
        a += byte_alignment;
    }
  }
  free(segs);
}

static void jitdump_emit_now(ptr co, void *arg) { jitdump_emit(co, *(U64 *)arg); }

static U64 jitdump_open_time;

/* open the file before the boot files load, so that code they create and
   run gets records too (vfasl'd boot code, which does not go through
   S_code, is covered by the walk in S_jitdump_boot_done) */
static void jitdump_open(void) {
  const char *dir = getenv("CHEZ_JITDUMP");
  char path[4096];
  int fd;
  struct { U32 magic, version, total_size, elf_mach, pad1, pid; U64 timestamp, flags; } hdr;
  if (dir == NULL || *dir == 0 || jitdump_f != NULL) return;
#if defined(__x86_64__)
  jitdump_tsc = getenv("CHEZ_JITDUMP_TSC") != NULL;
#endif
  { const char *nm = getenv("CHEZ_JITDUMP_NO_MOVES"); jitdump_moves = nm == NULL || *nm == 0; }
  jitdump_pid = getpid();
  snprintf(path, sizeof(path), "%s/jit-%d.dump", dir, (int)jitdump_pid);
  fd = open(path, O_CREAT|O_TRUNC|O_RDWR, 0666);
  if (fd < 0) { perror(path); return; }
  /* perf finds the file by this executable mapping of it */
  jitdump_marker = mmap(NULL, sysconf(_SC_PAGESIZE), PROT_READ|PROT_EXEC, MAP_PRIVATE, fd, 0);
  jitdump_f = fdopen(fd, "wb");
  if (jitdump_f == NULL) { close(fd); return; }
  hdr.magic = 0x4A695444; hdr.version = 1; hdr.total_size = sizeof(hdr);
  hdr.elf_mach = JITDUMP_ELF_MACH; hdr.pad1 = 0; hdr.pid = (U32)jitdump_pid;
  hdr.timestamp = jitdump_open_time = jitdump_now();
  hdr.flags = jitdump_tsc ? 1 : 0; /* JITDUMP_FLAGS_ARCH_TIMESTAMP */
  fwrite(&hdr, sizeof(hdr), 1, jitdump_f);
  fflush(jitdump_f);
  s_thread_mutex_init(&jitdump_mutex);
  jitdump_ready = 1;
  { const char *lz = getenv("CHEZ_JITDUMP_LAZY");
    jitdump_tracking = lz == NULL || *lz == 0;
    jitdump_lazy_every = lz != NULL && strcmp(lz, "all") == 0; }
}

/* once the boot files are loaded: record all code there is, stamped with
   the time the file was opened, since code that came straight from a boot
   file has been there since it was read; code that was created or moved
   during boot also has records with later times, which take precedence */
void S_jitdump_boot_done(void) {
  if (!jitdump_tracking) return;
  s_thread_mutex_lock(&jitdump_mutex);
  jitdump_each_code(jitdump_emit_now, &jitdump_open_time);
  fflush(jitdump_f);
  s_thread_mutex_unlock(&jitdump_mutex);
}

/* magic-trace snapshots its trace buffer when this is called (it finds
   the function by name, so the name and arguments are its protocol) */
void magic_trace_stop_indicator(U64 start_tsc, U64 arg) __attribute__((noinline, used));
void magic_trace_stop_indicator(U64 start_tsc, U64 arg) {
  __asm__ volatile("" :: "r"(start_tsc), "r"(arg) : "memory");
}

static U64 jitdump_snap_time;

/* magic-trace watches for the call to magic_trace_stop_indicator with a
   breakpoint on the main thread only (the kernel will not map the buffer of
   a breakpoint that other threads inherit), so another thread has the main
   thread make the call from a signal handler, and waits for it (up to 50 ms) */
static U64 magic_trace_sig_start, magic_trace_sig_arg;
static volatile int magic_trace_sig_done;
static pthread_mutex_t magic_trace_sig_mutex = PTHREAD_MUTEX_INITIALIZER;
static void magic_trace_sig_handler(UNUSED int sig) {
  magic_trace_stop_indicator(magic_trace_sig_start, magic_trace_sig_arg);
  __atomic_store_n(&magic_trace_sig_done, 1, __ATOMIC_RELEASE);
}
static void magic_trace_indicate(U64 start_tsc, U64 arg) {
  static int installed = 0;
  pid_t pid = getpid();
  double deadline;
  if ((pid_t)syscall(SYS_gettid) == pid) {
    magic_trace_stop_indicator(start_tsc, arg);
    return;
  }
  pthread_mutex_lock(&magic_trace_sig_mutex);
  if (!installed) {
    struct sigaction sa;
    memset(&sa, 0, sizeof(sa));
    sa.sa_handler = magic_trace_sig_handler;
    sa.sa_flags = SA_RESTART;
    sigemptyset(&sa.sa_mask);
    sigaction(SIGRTMIN + 6, &sa, NULL);
    installed = 1;
  }
  magic_trace_sig_start = start_tsc;
  magic_trace_sig_arg = arg;
  __atomic_store_n(&magic_trace_sig_done, 0, __ATOMIC_RELEASE);
  syscall(SYS_tgkill, pid, pid, SIGRTMIN + 6);
  deadline = magic_trace_ms() + 50;
  while (!__atomic_load_n(&magic_trace_sig_done, __ATOMIC_ACQUIRE) && magic_trace_ms() < deadline) {
    struct timespec ts = { 0, 10000 };
    nanosleep(&ts, NULL);
  }
  pthread_mutex_unlock(&magic_trace_sig_mutex);
}

static void s_magic_trace_snapshot(U64 start_tsc, U64 arg) {
  /* magic-trace reads the arguments as OCaml ints, which are tagged */
  magic_trace_indicate((start_tsc << 1) | 1, (arg << 1) | 1);
  if (jitdump_ready && !jitdump_tracking && (jitdump_lazy_every || !jitdump_lazy_done)) {
    const char *d = getenv("CHEZ_MAGIC_TRACE_DELAY_MS");
    long ms = d && *d ? atol(d) : 100;
    U64 t;
    struct timespec ts;
    if (ms > 0) { ts.tv_sec = ms / 1000; ts.tv_nsec = (ms % 1000) * 1000000L; nanosleep(&ts, NULL); }
    s_thread_mutex_lock(&jitdump_mutex);
    t = jitdump_snap_time ? jitdump_snap_time : jitdump_open_time;
    jitdump_each_code(jitdump_emit_now, &t);
    jitdump_snap_time = jitdump_now();
    jitdump_lazy_done = 1;
    fflush(jitdump_f);
    s_thread_mutex_unlock(&jitdump_mutex);
  }
}

void S_jitdump_foreign_init(void) {
  Sforeign_symbol("(cs)magic_trace_snapshot", (void *)s_magic_trace_snapshot);
  Sforeign_symbol("(cs)magic_trace_tsc", (void *)s_magic_trace_tsc);
}

static void jitdump_map_line(ptr co, void *arg) {
  char name[1024];
  jitdump_name(co, name, sizeof(name));
  fprintf((FILE *)arg, "%lx %lx %s\n", (unsigned long)(uptr)CODEENTRYPOINT(co), (unsigned long)CODELEN(co), name);
}

static void jitdump_exit(void) {
  if (jitdump_f != NULL) {
    S_jitdump_before_gc();
    fflush(jitdump_f);
  }
  if (getenv("CHEZ_PERF_MAP") != NULL) {
    char path[64]; FILE *f;
    snprintf(path, sizeof(path), "/tmp/perf-%d.map", (int)getpid());
    if ((f = fopen(path, "w")) != NULL) { jitdump_each_code(jitdump_map_line, f); fclose(f); }
  }
}

static void S_jitdump_init(void) {
  const char *g = getenv("CHEZ_MAGIC_TRACE_GC_MS");
  if (g && *g) magic_trace_gc_ms = atof(g);
  g = getenv("CHEZ_MAGIC_TRACE_RENDEZVOUS_MS");
  if (g && *g) magic_trace_rdv_ms = atof(g);
  g = getenv("CHEZ_MAGIC_TRACE_RENDEZVOUS_SKIP");
  if (g && *g) magic_trace_rdv_skip = atol(g);
  g = getenv("CHEZ_GC_RENDEZVOUS_LOG");
  magic_trace_rdv_log = g && *g;
  if (getenv("CHEZ_JITDUMP") != NULL || getenv("CHEZ_PERF_MAP") != NULL) atexit(jitdump_exit);
  jitdump_open();
}

#else
static void s_magic_trace_snapshot(U64 start_tsc, U64 arg) { (void)start_tsc; (void)arg; }
static U64 s_magic_trace_tsc(void) { return 0; }
void S_jitdump_foreign_init(void) {
  Sforeign_symbol("(cs)magic_trace_snapshot", (void *)s_magic_trace_snapshot);
  Sforeign_symbol("(cs)magic_trace_tsc", (void *)s_magic_trace_tsc);
}
static void S_jitdump_init(void) { }
static void jitdump_collect_requested(void) { }
void S_jitdump_boot_done(void) { }
void S_jitdump_code_created(UNUSED ptr co) { }
void S_jitdump_code_moved(UNUSED ptr oldco, UNUSED ptr co) { }
void S_jitdump_before_gc(void) { }
void S_jitdump_after_gc(void) { }
#endif
