/* jitdump.inc: tell profilers where Scheme code is, as it is created and
 * as the collector moves it.
 *
 * CHEZ_JITDUMP=DIR writes DIR/jit-PID.dump in the jitdump format that
 * `perf inject --jit` reads (record with `perf record -k mono`). The
 * file starts with every code object in the heap once the boot files are
 * loaded, then gets a load record for code as it is created (written
 * before the next collection, once the code is filled in, but stamped
 * with the time it was created) and again for code each time the
 * collector moves it, so that an address is
 * named by whichever code was there when a sample was taken.
 *
 * CHEZ_PERF_MAP=1 writes /tmp/perf-PID.map at exit, naming code where it
 * is at that point (perf report reads it without any extra steps).
 *
 * Linux only.
 */

#if defined(__linux__) && defined(PTHREADS)

#include <time.h>
#include <sys/mman.h>
#include <sys/syscall.h>
#include <unistd.h>
#include <fcntl.h>

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
static IBOOL jitdump_ready;
static ptr *jitdump_pending; static U64 *jitdump_pending_t; static uptr jitdump_npending, jitdump_maxpending;
static ptr *jitdump_moved; static uptr jitdump_nmoved, jitdump_maxmoved;

static U64 jitdump_now(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (U64)ts.tv_sec * 1000000000ULL + (U64)ts.tv_nsec;
}

/* the code object's name, as perf should show it */
static int jitdump_name(ptr co, char *buf, int max) {
  ptr name = CODENAME(co);
  iptr n, i; int len = 0;
  if (Sstringp(name)) {
    n = Sstring_length(name);
    for (i = 0; i < n && len < max - 1; i++) {
      string_char c = Sstring_ref(name, i);
      buf[len++] = (c < 32 || c > 126) ? '_' : (char)c;
    }
  }
  if (len == 0) len = snprintf(buf, max, "[anonymous]");
  buf[len] = 0;
  return len;
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

/* a code object just allocated; it gets its record once it is filled in */
void S_jitdump_code_created(ptr co) {
  if (!jitdump_ready) return;
  s_thread_mutex_lock(&jitdump_mutex);
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

/* a code object that the collector has just swept into a new place */
void S_jitdump_code_moved(ptr co) {
  if (!jitdump_ready) return;
  s_thread_mutex_lock(&jitdump_mutex);
  jitdump_push(&jitdump_moved, &jitdump_nmoved, &jitdump_maxmoved, co);
  s_thread_mutex_unlock(&jitdump_mutex);
}

/* before a collection, record code created since the last one (now filled in) */
void S_jitdump_before_gc(void) {
  uptr i;
  if (!jitdump_ready) return;
  s_thread_mutex_lock(&jitdump_mutex);
  for (i = 0; i < jitdump_npending; i++) jitdump_emit(jitdump_pending[i], jitdump_pending_t[i]);
  jitdump_npending = 0;
  jitdump_nmoved = 0;
  s_thread_mutex_unlock(&jitdump_mutex);
}

/* after a collection, record where it put the code it moved */
void S_jitdump_after_gc(void) {
  uptr i; U64 t;
  if (!jitdump_ready) return;
  s_thread_mutex_lock(&jitdump_mutex);
  t = jitdump_now();
  for (i = 0; i < jitdump_nmoved; i++) {
    ptr co = jitdump_moved[i];
    seginfo *si = MaybeSegInfo(ptr_get_segment(co));
    if (si != NULL && si->space == space_code && !si->use_marks) jitdump_emit(co, t);
  }
  jitdump_nmoved = 0;
  fflush(jitdump_f);
  s_thread_mutex_unlock(&jitdump_mutex);
}

/* ---------------------------------------------------------------------- */
/* walking all code in the heap */

static IBOOL jitdump_codep(ptr co) {
  iptr len, nfree; ptr name;
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

/* once the boot files are loaded: start the file with all code there is */
void S_jitdump_boot_done(void) {
  const char *dir = getenv("CHEZ_JITDUMP");
  char path[4096];
  int fd;
  struct { U32 magic, version, total_size, elf_mach, pad1, pid; U64 timestamp, flags; } hdr;
  U64 t;
  if (dir == NULL || *dir == 0 || jitdump_f != NULL) return;
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
  hdr.timestamp = jitdump_now(); hdr.flags = 0;
  fwrite(&hdr, sizeof(hdr), 1, jitdump_f);
  s_thread_mutex_init(&jitdump_mutex);
  t = jitdump_now();
  jitdump_each_code(jitdump_emit_now, &t);
  fflush(jitdump_f);
  jitdump_ready = 1;
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
  if (getenv("CHEZ_JITDUMP") != NULL || getenv("CHEZ_PERF_MAP") != NULL) atexit(jitdump_exit);
}

#else
static void S_jitdump_init(void) { }
void S_jitdump_boot_done(void) { }
void S_jitdump_code_created(UNUSED ptr co) { }
void S_jitdump_code_moved(UNUSED ptr co) { }
void S_jitdump_before_gc(void) { }
void S_jitdump_after_gc(void) { }
#endif
