/* sampler.inc: a statistical profiler that records Scheme call stacks
 * by walking Chez's own frame metadata.
 *
 * Chez's return points carry the size of the frame they return into (and
 * the offset back to their code object), so a stack can be walked exactly
 * without frame pointers or DWARF unwind tables, and without changing the
 * generated code.
 *
 * Set CHEZ_SAMPLE_STACKS=FILE to sample every Scheme thread's CPU time.
 * At exit, FILE gets folded stacks: one line per distinct stack, outermost
 * frame first, separated by `;`, then a count. flamegraph.pl, inferno,
 * and speedscope read that format. Other settings:
 *
 *   CHEZ_SAMPLE_HZ=N       samples per second of CPU time (default 999)
 *   CHEZ_SAMPLE_EVENT=E    "task-clock" (default) or "cycles" use a perf
 *                          event on each thread; "timer" uses a POSIX
 *                          CPU-time timer, which needs no perf access but
 *                          is limited to the kernel tick rate. task-clock
 *                          falls back to the timer when perf_event_open
 *                          is not allowed (e.g. perf_event_paranoid > 2).
 *   CHEZ_SAMPLE_THREADS=1  start each stack with the thread's index
 *   CHEZ_SAMPLE_DEBUG=1    report the sampling mode and walk statistics
 *   CHEZ_SAMPLE_MARK=0     do not mark frames by origin (see below)
 *   CHEZ_SAMPLE_SRCLOC=0   do not add `@file:line` to names of code that
 *                          has procedure source information; `full` adds
 *                          `@path#start-end` (character positions) instead
 *
 * Frames are marked by where their code came from, with the annotations
 * that flamegraph.pl's `--colors java` palette understands: code loaded
 * from boot files (Chez itself, and Racket CS's runtime, expander, and
 * I/O layers) ends in `_[i]`, and other Scheme code in `_[j]`. C frames
 * start with `[C]`. Tools can use the marks to hide runtime glue such as
 * dynamic-wind and anonymous thunks between frames of the program.
 *
 * Programs can also start and stop sampling themselves, through foreign
 * entries (use `foreign-procedure`):
 *
 *   "(cs)sampler_start" (int hz) -> int   start sampling the calling
 *                          thread (and threads created while on); returns
 *                          0 for the timer, 1 task-clock, 2 cycles, -1 if
 *                          sampling is unavailable
 *   "(cs)sampler_stop" () -> void         stop sampling
 *   "(cs)sampler_take" () -> scheme-object  the samples so far, as a
 *                          bytevector of folded stacks, and clear them
 *   "(cs)sampler_config" (int mark, int srcloc) -> void  set what names
 *                          carry: origin marks (0 or 1), and source
 *                          locations (0 none, 1 file:line, 2 full)
 *
 * Walk: from the interrupted frame register through stack segments and
 * continuation links. When that chain ends, the walk continues with
 * Racket CS's metacontinuation frames: a virtual register holding a list
 * of records whose second field is the continuation to resume. A sample
 * in C code records the C frames (named at exit from the executable's
 * symbol table; frame-pointer builds of the C runtime give the whole C
 * chain) and then the Scheme stack from the frame that Chez saved in the
 * thread context when it called out to C.
 *
 * Names are copied at sample time, so code that the collector moves or
 * frees later is still named correctly.
 *
 * Linux on x86_64 and arm64.
 */

#if defined(__linux__) && (defined(__x86_64__) || defined(__aarch64__)) && defined(PTHREADS)

#include <signal.h>
#include <time.h>
#include <sys/mman.h>
#include <sys/time.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <unistd.h>
#include <sys/ioctl.h>
#include <ucontext.h>
#include <fcntl.h>
#include <elf.h>
#include <linux/perf_event.h>

/* system.h is included first, without _GNU_SOURCE, so spell out what we need */
#ifndef F_SETSIG
# define F_SETSIG 10
#endif
#ifndef F_SETOWN_EX
# define F_SETOWN_EX 15
# define F_OWNER_TID 0
struct f_owner_ex { int type; pid_t pid; };
#endif
#ifndef SIGEV_THREAD_ID
# define SIGEV_THREAD_ID 4
#endif
#ifndef sigev_notify_thread_id
# define sigev_notify_thread_id _sigev_un._tid
#endif
typedef struct { const char *dli_fname; void *dli_fbase; const char *dli_sname; void *dli_saddr; } sampler_dl_info;
extern int dladdr(const void *addr, sampler_dl_info *info);

#if defined(__x86_64__)
# define SAMPLER_PC(uc) ((uptr)(uc)->uc_mcontext.gregs[16]) /* REG_RIP */
# define SAMPLER_SFP(uc) ((uptr)(uc)->uc_mcontext.gregs[5]) /* REG_R13 */
# define SAMPLER_TC(uc) ((ptr)(uc)->uc_mcontext.gregs[6])   /* REG_R14 */
# define SAMPLER_CP(uc) ((ptr)(uc)->uc_mcontext.gregs[7])   /* REG_R15 */
# define SAMPLER_FP(uc) ((uptr)(uc)->uc_mcontext.gregs[10]) /* REG_RBP */
# define SAMPLER_SP(uc) ((uptr)(uc)->uc_mcontext.gregs[15]) /* REG_RSP */
# define SAMPLER_LR(uc) ((uptr)0)
#else
# define SAMPLER_PC(uc) ((uptr)(uc)->uc_mcontext.pc)
# define SAMPLER_SFP(uc) ((uptr)(uc)->uc_mcontext.regs[20])
# define SAMPLER_TC(uc) ((ptr)(uc)->uc_mcontext.regs[19])
# define SAMPLER_CP(uc) ((ptr)(uc)->uc_mcontext.regs[26])
# define SAMPLER_FP(uc) ((uptr)(uc)->uc_mcontext.regs[29])
# define SAMPLER_SP(uc) ((uptr)(uc)->uc_mcontext.sp)
# define SAMPLER_LR(uc) ((uptr)(uc)->uc_mcontext.regs[30])
#endif

#define SAMPLER_MAX_DEPTH 1024
#define SAMPLER_NAME_MAX 255
#define SAMPLER_C_DEPTH 64

/* ---------------------------------------------------------------------- */
/* name table: interned strings, insert-only and lock-free */

#define SAMPLER_NSLOTS ((uptr)1 << 20)
static U64 *sampler_slots;            /* (hash << 32) | offset into pool */
static char *sampler_pool;            /* entries: 1 length byte, then chars */
static uptr sampler_pool_size, sampler_pool_used = 1;

static U32 sampler_hash(const char *s, int n) {
  U32 h = 2166136261u; int i;
  for (i = 0; i < n; i++) h = (h ^ (unsigned char)s[i]) * 16777619u;
  return h | 1;
}

/* offset of the interned copy of s, or 0 if the table is full */
static U32 sampler_intern(const char *s, int n) {
  U32 h = sampler_hash(s, n);
  uptr i = h & (SAMPLER_NSLOTS - 1), probes;
  U32 off = 0;
  for (probes = 0; probes < SAMPLER_NSLOTS; probes++, i = (i + 1) & (SAMPLER_NSLOTS - 1)) {
    U64 slot = __atomic_load_n(&sampler_slots[i], __ATOMIC_ACQUIRE);
    if (slot == 0) {
      if (off == 0) {
        uptr at = __atomic_fetch_add(&sampler_pool_used, (uptr)n + 1, __ATOMIC_RELAXED);
        if (at + n + 1 > sampler_pool_size || at > 0xffffffffu) return 0;
        sampler_pool[at] = (char)n;
        memcpy(sampler_pool + at + 1, s, n);
        off = (U32)at;
      }
      if (__atomic_compare_exchange_n(&sampler_slots[i], &slot, ((U64)h << 32) | off,
                                      0, __ATOMIC_RELEASE, __ATOMIC_ACQUIRE))
        return off;
      /* lost a race for this slot; slot now holds the winner */
    }
    if ((U32)(slot >> 32) == h) {
      U32 o = (U32)slot;
      if ((unsigned char)sampler_pool[o] == n && memcmp(sampler_pool + o + 1, s, n) == 0)
        return o;
    }
  }
  return 0;
}

/* ---------------------------------------------------------------------- */
/* sample buffer: records of [count, name offsets outermost first] */

static U32 *sampler_buf;
static uptr sampler_buf_words, sampler_buf_used;
static uptr sampler_dropped;
static const char *sampler_path;
static IBOOL sampler_prefix_thread;
static int sampler_mode;               /* 0 = timer, 1 = task-clock, 2 = cycles */
static long sampler_hz;
static uptr sampler_stats[8];          /* walk end reasons, for CHEZ_SAMPLE_DEBUG */
static int sampler_mc_vreg = -1;       /* virtual register with Racket's metacontinuation */
static volatile int sampler_on;
static int sampler_debug;
static int sampler_thread_count;
static int sampler_mark = 1;
static int sampler_srcloc = 1;
static volatile int sampler_active;    /* handlers between start and record */

enum { end_root, end_bad_ret, end_bad_sfp, end_bad_tc, end_depth, end_c_only, end_metak, end_samples };

static __thread int sampler_tid_index;
static __thread int sampler_perf_fd = -1;
static __thread uptr sampler_stack_lo, sampler_stack_hi;
static __thread timer_t sampler_timer;
static __thread IBOOL sampler_timer_on;
/* With a perf event, a slow CPU-time timer on the same thread re-arms the
   event when no sample has arrived since its last tick: the event can stay
   disabled after an overflow (seen on KVM guests), which would otherwise
   end sampling for the thread. */
#define SAMPLER_WATCHDOG_HZ 20
static __thread uptr sampler_perf_hits, sampler_watchdog_last;
static uptr sampler_rearms;
static __thread U32 sampler_frames[SAMPLER_MAX_DEPTH + SAMPLER_C_DEPTH + 16];
static __thread struct { uptr lo, hi; ptr co; } sampler_code_cache[1024];
static __thread struct { uptr d, name; iptr len, free; } sampler_diag[4];
static __thread int sampler_diag_n;

/* ---------------------------------------------------------------------- */
/* reading the heap */

/* set while the collector runs: stacks and continuations are being moved,
   so a sample then records only its C frames */
static volatile int sampler_in_gc;

static IBOOL sampler_code_addr(uptr a) {
  seginfo *si = MaybeSegInfo(addr_get_segment(a));
  return si != NULL && si->space == space_code;
}

static IBOOL sampler_heap_addr(uptr a) {
  return MaybeSegInfo(addr_get_segment(a)) != NULL;
}

/* code object for a return address, via the return point's top link */
static ptr sampler_ret_code(uptr ret) {
  iptr co = ENTRYOFFSET(ret) + (ret - (uptr)ENTRYOFFSETADDR(ret));
  return (ptr)(ret - co);
}

/* whether ret can be read as a return address: the return-point header
   before it must be in code space too, since a stale word in a frame can
   point anywhere into a code segment */
static IBOOL sampler_ret_ok(uptr ret) {
  return sampler_code_addr(ret) && sampler_code_addr(ret - size_rp_header);
}

static IBOOL sampler_continuationp(ptr k) {
  ptr co;
  if (!Sprocedurep(k) || !sampler_heap_addr((uptr)k)) return 0;
  co = CLOSCODE(k);
  return sampler_heap_addr((uptr)co) && Scodep(co)
    && ((CODETYPE(co) >> code_flags_offset) & code_flag_continuation) != 0;
}

static IBOOL sampler_code_contains(ptr co, uptr pc) {
  return pc >= (uptr)CODEENTRYPOINT(co) && pc < (uptr)CODEENTRYPOINT(co) + CODELEN(co);
}

/* whether a word that looks like a code header really starts one: machine
   code can contain such words, so check the fields after it too */
static IBOOL sampler_plausible_code(ptr co, uptr pc) {
  ptr name;
  iptr len, nfree;
  if (!sampler_heap_addr((uptr)co + code_data_disp)) return 0;
  len = CODELEN(co); nfree = CODEFREE(co);
  if (len <= 0 || len > ((iptr)1 << 26) || !sampler_code_contains(co, pc)) return 0;
  if (nfree < 0 || nfree > ((iptr)1 << 20)) return 0;
  name = CODENAME(co);
  if (name != Sfalse
      && !(((uptr)name & mask_typed_object) == type_typed_object && sampler_heap_addr((uptr)name) && Sstringp(name)))
    return 0;
  return 1;
}

/* the code object containing pc, which is in a code segment */
static ptr sampler_code_at(uptr pc, ptr cp) {
  uptr slot = (pc >> 5) & 1023, a;
  ptr co;
  if (Sprocedurep(cp) && sampler_heap_addr((uptr)cp)) {
    co = CLOSCODE(cp);
    if (sampler_heap_addr((uptr)co) && Scodep(co) && sampler_code_contains(co, pc)) return co;
  }
  if (pc >= sampler_code_cache[slot].lo && pc < sampler_code_cache[slot].hi) {
    co = sampler_code_cache[slot].co;
    /* the collector may have moved or reused it */
    if (sampler_code_addr((uptr)co)
        && (CODETYPE(co) & mask_code) == type_code && sampler_code_contains(co, pc))
      return co;
  }
  /* look back from pc for the code object's header; every word from the
     object's start to pc is inside the object, so it is mapped */
  for (a = pc & ~(uptr)(ptr_bytes - 1); pc - a < ((uptr)1 << 24); a -= ptr_bytes) {
    if ((a & (bytes_per_segment - 1)) == 0 && !sampler_heap_addr(a - ptr_bytes)) break;
    if ((*(uptr *)a & mask_code) == type_code) {
      co = (ptr)(a - code_type_disp);
      if (sampler_plausible_code(co, pc)) {
        sampler_code_cache[slot].lo = (uptr)CODEENTRYPOINT(co);
        sampler_code_cache[slot].hi = (uptr)CODEENTRYPOINT(co) + CODELEN(co);
        sampler_code_cache[slot].co = co;
        return co;
      }
      if (sampler_debug && sampler_diag_n < 4) {
        sampler_diag[sampler_diag_n].d = pc - a;
        sampler_diag[sampler_diag_n].len = CODELEN(co);
        sampler_diag[sampler_diag_n].free = CODEFREE(co);
        sampler_diag[sampler_diag_n].name = (uptr)CODENAME(co);
        sampler_diag_n++;
      }
    }
  }
  return NULL;
}

static U32 sampler_hex_name(const char *prefix, uptr a) {
  char buf[48];
  int n = snprintf(buf, sizeof(buf), "%s0x%lx", prefix, (unsigned long)a);
  return sampler_intern(buf, n);
}

/* field i of record r, or NOFIELD when r is not a record with that field
   (NULL would be the fixnum 0) */
#define NOFIELD ((ptr)(uptr)1)
static ptr sampler_field(ptr r, iptr i) {
  ptr rtd, size;
  if (!sampler_heap_addr((uptr)r) || !Srecordp(r)) return NOFIELD;
  rtd = RECORDINSTTYPE(r);
  if (!sampler_heap_addr((uptr)rtd) || !Srecordp(rtd)) return NOFIELD;
  size = RECORDDESCSIZE(rtd);
  if (!Sfixnump(size) || i >= UNFIX(size) / ptr_bytes - 1) return NOFIELD;
  return RECORDINSTIT(r, i);
}

/* append "@file:line" (or "@file#pos") for code compiled with procedure source information
   (Racket CS's default for program code): the code's info is a code-info
   record whose first field is a source object (sfd, bfp, efp, and for
   source-2d also line and column); the sfd's path is a string, or for
   Racket a srcloc record holding a path record holding bytes. */
static int sampler_source_label(ptr co, char *buf, int len, int max) {
  ptr info = CODEINFO(co), src, sfd, path, line;
  char file[256]; int flen = 0, n, full = sampler_srcloc == 2;
  iptr i, plen;
  const char *base;
  if (info == Sfalse || (src = sampler_field(info, 0)) == NOFIELD) return len;
  if ((sfd = sampler_field(src, 0)) == NOFIELD || (path = sampler_field(sfd, 0)) == NOFIELD) return len;
  for (n = 0; n < 3 && sampler_heap_addr((uptr)path) && Srecordp(path); n++)
    if ((path = sampler_field(path, 0)) == NOFIELD) return len;
  if (!sampler_heap_addr((uptr)path)) return len;
  if (Sstringp(path)) {
    plen = Sstring_length(path);
    for (i = plen; !full && i > 0 && Sstring_ref(path, i - 1) != '/'; i--) ;
    if (full) i = 0;
    for (; i < plen && flen < (int)sizeof(file) - 1; i++) {
      string_char c = Sstring_ref(path, i);
      file[flen++] = (c == ';' || c == ' ' || c < 32 || c > 126) ? '_' : (char)c;
    }
  } else if (Sbytevectorp(path)) {
    const char *b = (const char *)Sbytevector_data(path);
    plen = Sbytevector_length(path);
    for (base = b + plen; !full && base > b && base[-1] != '/'; base--) ;
    if (full) base = b;
    for (; base < b + plen && flen < (int)sizeof(file) - 1; base++)
      file[flen++] = (*base == ';' || *base == ' ' || *base < 32 || *base > 126) ? '_' : *base;
  } else
    return len;
  if (flen == 0) return len;
  file[flen] = 0;
  if (full) {
    ptr bfp = sampler_field(src, 1), efp = sampler_field(src, 2);
    if (bfp == NOFIELD || efp == NOFIELD || !Sfixnump(bfp) || !Sfixnump(efp)) return len;
    n = snprintf(buf + len, max - len, "@%s#%ld-%ld", file, (long)UNFIX(bfp), (long)UNFIX(efp));
    return (n > 0 && len + n < max) ? len + n : len;
  }
  line = sampler_field(src, 3);
  if (line != NOFIELD && Sfixnump(line) && UNFIX(line) > 0)
    n = snprintf(buf + len, max - len, "@%s:%ld", file, (long)UNFIX(line));
  else if ((line = sampler_field(src, 1)) != NOFIELD && Sfixnump(line))
    /* no line: the character position, as Chez prints source objects */
    n = snprintf(buf + len, max - len, "@%s#%ld", file, (long)UNFIX(line));
  else
    n = snprintf(buf + len, max - len, "@%s", file);
  return (n > 0 && len + n < max) ? len + n : len;
}

/* interned name of code object co, or of the address a when co has none */
static U32 sampler_code_name(ptr co, uptr a) {
  char buf[SAMPLER_NAME_MAX];
  ptr name; iptr n, i, start; int len = 0;
  if (co == NULL || !sampler_heap_addr((uptr)co) || !Scodep(co)) return sampler_hex_name("", a);
  name = CODENAME(co);
  if (name == Sfalse) {
    memcpy(buf, "[anonymous]", 11); len = 11;
    if (sampler_srcloc) len = sampler_source_label(co, buf, len, SAMPLER_NAME_MAX - 5);
    if (sampler_mark) {
      seginfo *si = MaybeSegInfo(addr_get_segment((uptr)co));
      memcpy(buf + len, (si != NULL && si->generation == static_generation) ? "_[i]" : "_[j]", 4);
      len += 4;
    }
    return sampler_intern(buf, len);
  }
  if (!sampler_heap_addr((uptr)name) || !Sstringp(name)) return sampler_hex_name("", a);
  n = Sstring_length(name);
  /* keep the end of long names, which for Racket holds the line and column */
  start = n > SAMPLER_NAME_MAX - 1 ? n - (SAMPLER_NAME_MAX - 1) : 0;
  for (i = start; i < n; i++) {
    string_char c = Sstring_ref(name, i);
    buf[len++] = (c == ';' || c == ' ' || c < 32 || c > 126) ? '_' : (char)c;
  }
  if (len == 0) return sampler_hex_name("", a);
  /* names that start with `[` already carry their source location */
  if (sampler_srcloc && buf[0] != '[') len = sampler_source_label(co, buf, len, SAMPLER_NAME_MAX - 5);
  if (sampler_mark && len + 4 < SAMPLER_NAME_MAX) {
    seginfo *si = MaybeSegInfo(addr_get_segment((uptr)co));
    memcpy(buf + len, (si != NULL && si->generation == static_generation) ? "_[i]" : "_[j]", 4);
    len += 4;
  }
  return sampler_intern(buf, len);
}

/* Racket CS's metacontinuation: a list of records whose second field is
   the continuation to resume, in one of the virtual registers */
static IBOOL sampler_metak_listp(ptr v) {
  ptr e;
  if (!Spairp(v) || !sampler_heap_addr((uptr)v)) return 0;
  e = Scar(v);
  return ((uptr)e & mask_typed_object) == type_typed_object && sampler_heap_addr((uptr)e)
    && sampler_continuationp(sampler_field(e, 1));
}

static ptr sampler_metak_list(ptr tc) {
  int r = sampler_mc_vreg;
  if (r >= 0) {
    ptr v = VIRTREG(tc, r);
    if (v == Snil || sampler_metak_listp(v)) return v;
  }
  for (r = 0; r < virtual_register_count; r++) {
    ptr v = VIRTREG(tc, r);
    if (sampler_metak_listp(v)) { sampler_mc_vreg = r; return v; }
  }
  return Snil;
}

/* A non-tail call bumps the frame register, sets up the call, and then
   stores the return address at the new frame's base; until that store,
   the word there is stale. When pc is in that window, return the address
   that is about to be stored, found by looking ahead for the store; 0
   otherwise. `limit` bounds the look-ahead (the end of the code object). */
static uptr sampler_pending_ret(ucontext_t *uc, uptr pc, uptr limit) {
#if defined(__x86_64__)
  const unsigned char *b = (const unsigned char *)pc;
  static const int greg[16] = { 13, 14, 12, 11, 15, 10, 9, 8, 0, 1, 2, 3, 4, 5, 6, 7 };
  uptr i, n = limit - pc < 48 ? limit - pc : 48;
  for (i = 0; i + 11 <= n; i++) {
    /* add r13, imm: the frame is not bumped yet */
    if (b[i] == 0x49 && (b[i+1] == 0x83 || b[i+1] == 0x81) && b[i+2] == 0xc5) return 0;
    /* lea reg, [rip + disp32]; mov [r13 + 0], reg */
    if ((b[i] & 0xfb) == 0x48 && b[i+1] == 0x8d && (b[i+2] & 0xc7) == 0x05
        && (b[i+7] & 0xfb) == 0x49 && b[i+8] == 0x89 && (b[i+9] & 0xc7) == 0x45 && b[i+10] == 0
        && ((b[i+2] >> 3) & 7) == ((b[i+9] >> 3) & 7) && ((b[i] ^ b[i+7]) & 4) == 0) {
      I32 disp; memcpy(&disp, b + i + 3, 4);
      return pc + i + 7 + (iptr)disp;
    }
  }
  /* pc at the store itself */
  if ((b[0] & 0xfb) == 0x49 && b[1] == 0x89 && (b[2] & 0xc7) == 0x45 && b[3] == 0) {
    int r = ((b[2] >> 3) & 7) | ((b[0] & 4) ? 8 : 0);
    return (uptr)uc->uc_mcontext.gregs[greg[r]];
  }
  return 0;
#else
  const U32 *w = (const U32 *)pc;
  uptr i, n = (limit - pc) / 4 < 16 ? (limit - pc) / 4 : 16;
  for (i = 0; i + 1 < n; i++) {
    U32 x = w[i];
    /* add x20, x20, #imm: the frame is not bumped yet */
    if ((x & 0xff8003ffu) == (0x91000000u | (20u << 5) | 20u)) return 0;
    /* adr xd, label; str xd, [x20] */
    if ((x & 0x9f000000u) == 0x10000000u && w[i+1] == (0xf9000000u | (20u << 5) | (x & 0x1f))) {
      iptr imm = (iptr)((((x >> 5) & 0x7ffff) << 2) | ((x >> 29) & 3));
      if (imm & ((iptr)1 << 20)) imm -= (iptr)1 << 21;
      return pc + i * 4 + imm;
    }
  }
  /* pc at the store itself */
  if (n > 0 && (w[0] & 0xffffffe0u) == (0xf9000000u | (20u << 5)))
    return (uptr)uc->uc_mcontext.regs[w[0] & 0x1f];
  return 0;
#endif
}

/* ---------------------------------------------------------------------- */
/* the walk */

typedef struct {
  ptr tc;
  uptr seg_base, seg_hi;  /* the stack segment holding the current frame */
  ptr k;            /* continuation whose stack we are in, or NULL for tc's stack */
  ptr mcs;          /* rest of the metacontinuation list, or #f before we look */
} sampler_pos;

/* move to the top frame of continuation `next` (or past it); returns 0 at the end */
static IBOOL sampler_enter(sampler_pos *p, ptr next, uptr *ret, uptr *sfp, int *why) {
  for (;;) {
    while (sampler_continuationp(next) && CONTLENGTH(next) != scaled_shot_1_shot_flag) {
      if (CONTCLENGTH(next) > 0) {
        p->k = next;
        p->seg_base = (uptr)CONTSTACK(next);
        p->seg_hi = p->seg_base + (uptr)CONTCLENGTH(next);
        if (!sampler_heap_addr(p->seg_base) || !sampler_heap_addr(p->seg_hi - 1)) { *why = end_bad_sfp; return 0; }
        *ret = (uptr)CONTRET(next);
        if (!sampler_ret_ok(*ret)) { *why = end_bad_ret; return 0; }
        *sfp = p->seg_hi - ENTRYFRAMESIZE(*ret);
        if (*sfp < p->seg_base || (*sfp & (sizeof(ptr) - 1)) != 0) { *why = end_bad_sfp; return 0; }
        return 1;
      }
      next = CONTLINK(next);
    }
    if (p->mcs == Sfalse) p->mcs = sampler_metak_list(p->tc);
    if (!sampler_metak_listp(p->mcs)) { *why = end_root; return 0; }
    next = sampler_field(Scar(p->mcs), 1);
    p->mcs = Scdr(p->mcs);
    if (sampler_continuationp(next)) sampler_stats[end_metak]++;
  }
}

/* append Scheme frames from the frame at sfp running at pc; returns new depth */
static int sampler_walk(ptr tc, uptr pc, uptr sfp, ptr cp, uptr pending, int depth, int *why) {
  sampler_pos p;
  uptr ret;
  sampler_diag_n = 0;
  {
    ptr lco = sampler_code_at(pc, cp);
    if (lco == NULL && sampler_debug) {
      char b[160]; int n = 0, i;
      for (i = 0; i < sampler_diag_n && n < 120; i++)
        n += snprintf(b + n, sizeof(b) - n, "[cand d=%lu len=%ld free=%ld name=%lx]", (unsigned long)sampler_diag[i].d,
                      (long)sampler_diag[i].len, (long)sampler_diag[i].free, (unsigned long)sampler_diag[i].name);
      if (n == 0) n = snprintf(b, sizeof(b), "[nocand]");
      if (sfp >= (uptr)SCHEMESTACK(tc) && sfp < (uptr)SCHEMESTACK(tc) + (uptr)SCHEMESTACKSIZE(tc) && sampler_code_addr(*(uptr *)sfp)) {
        ptr rco = sampler_ret_code(*(uptr *)sfp);
        n = snprintf(b, sizeof(b), "[retco d=%ld len=%ld hdr=%lx plaus=%d]", (long)(pc - ((uptr)rco - type_typed_object)),
                     (long)CODELEN(rco), (unsigned long)CODETYPE(rco), sampler_plausible_code(rco, pc));
      }
      if (n > (int)sizeof(b) - 1) n = sizeof(b) - 1;
      sampler_frames[depth++] = sampler_intern(b, n);
    }
    sampler_frames[depth++] = sampler_code_name(lco, pc);
  }
  p.tc = tc; p.k = NULL; p.mcs = Sfalse;
  p.seg_base = (uptr)SCHEMESTACK(tc);
  p.seg_hi = p.seg_base + (uptr)SCHEMESTACKSIZE(tc);
  if (!sampler_heap_addr(p.seg_base)) { *why = end_bad_sfp; return depth; }
  while (depth < SAMPLER_MAX_DEPTH) {
    /* never read outside the segment: during a collection, or with a stale
       frame register, sfp can point anywhere */
    if (!(sfp >= p.seg_base && sfp < p.seg_hi && (sfp & (sizeof(ptr) - 1)) == 0)) { *why = end_bad_sfp; return depth; }
    if (sfp > p.seg_base) {
      if (pending != 0) { ret = pending; pending = 0; }
      else ret = *(uptr *)sfp;
      if (!sampler_ret_ok(ret)) {
        *why = end_bad_ret;
        if (sampler_debug) {
          ptr co = sampler_code_at(pc, Sfalse);
          sampler_frames[depth++] = sampler_hex_name("[bad-ret]", ret);
          if (co != NULL && depth == 3) sampler_frames[depth++] = sampler_hex_name("[pc-offset]", pc - (uptr)CODEENTRYPOINT(co));
        }
        return depth;
      }
      sfp -= ENTRYFRAMESIZE(ret);
      if (sfp < p.seg_base) { *why = end_bad_sfp; return depth; }
    } else {
      /* bottom of a segment: continue with the continuation it links to */
      if (!sampler_enter(&p, p.k == NULL ? STACKLINK(tc) : CONTLINK(p.k), &ret, &sfp, why))
        return depth;
    }
    sampler_frames[depth++] = sampler_code_name(sampler_ret_code(ret), ret);
  }
  *why = end_depth;
  return depth;
}

/* The collector runs with Scheme stopped, so the collecting thread's Scheme
   frames are walked once before it starts, and samples during the
   collection, in that thread or in the collector's sweeper threads, reuse
   them after their own C frames. */
static __thread volatile int sampler_busy;
static U32 sampler_gc_frames[SAMPLER_MAX_DEPTH + 8];
static int sampler_gc_depth, sampler_gc_why;

void S_sampler_gc_begin(void) {
  ptr tc = get_thread_context();
  sampler_gc_depth = 0;
  if (sampler_on && tc != NULL && sampler_stack_hi != 0) {
    uptr fp = (uptr)__builtin_frame_address(0), ra = 0;
    int n = 0, why = end_root, d;
    sampler_busy = 1;
    __atomic_signal_fence(__ATOMIC_SEQ_CST);
    while (n < SAMPLER_C_DEPTH && fp >= sampler_stack_lo && fp < sampler_stack_hi - 16 && (fp & 7) == 0) {
      uptr next = ((uptr *)fp)[0], r = ((uptr *)fp)[1];
      if (sampler_code_addr(r)) { ra = r; break; }
      if (next <= fp) break;
      fp = next; n++;
    }
    /* without C frame pointers, start from the code that called out to C,
       which a non-atomic foreign call leaves in the thread context */
    if (ra == 0 && sampler_heap_addr((uptr)CP(tc)) && Scodep(CP(tc)))
      ra = (uptr)CODEENTRYPOINT(CP(tc));
    if (ra != 0) {
      d = sampler_walk(tc, ra, (uptr)SFP(tc), Sfalse, 0, 0, &why);
      memcpy(sampler_gc_frames, sampler_frames, d * sizeof(U32));
      sampler_gc_depth = d; sampler_gc_why = why;
    }
    __atomic_signal_fence(__ATOMIC_SEQ_CST);
    sampler_busy = 0;
  }
  sampler_in_gc = 1;
}

void S_sampler_gc_end(void) { sampler_in_gc = 0; sampler_gc_depth = 0; }

static IBOOL sampler_setup(void);
extern int pthread_getattr_np(pthread_t, pthread_attr_t *);

/* For debuggers, on any architecture the sampler supports: prints the
   calling thread's Scheme stack, innermost first, with the same walk and
   names as the sampler. From gdb, stopped in C code that Scheme called
   (a breakpoint in S_gc, a crash in a foreign function):
     call (void)S_sampler_print_stack()
   or, stopped in Scheme code, give the pc and the frame register
   (%r13 on x86_64, x20 on arm64):
     call (void)S_sampler_print_stack_at($pc, $r13) */
void S_sampler_print_stack_at(uptr pc, uptr sfp) {
  ptr tc = get_thread_context();
  int d, i, why = end_root, n = 0;
  static const char *ends[] = { "root", "bad return address", "bad frame", "foreign thread", "depth limit", "C only", "metacontinuation" };
  if (tc == NULL) { fprintf(stderr, "no Scheme thread context\n"); return; }
  if (!sampler_setup()) { fprintf(stderr, "cannot set up the sampler's tables\n"); return; }
  if (sampler_stack_hi == 0) {
    pthread_attr_t attr; void *lo; size_t size;
    if (pthread_getattr_np(pthread_self(), &attr) == 0) {
      if (pthread_attr_getstack(&attr, &lo, &size) == 0) { sampler_stack_lo = (uptr)lo; sampler_stack_hi = (uptr)lo + size; }
      pthread_attr_destroy(&attr);
    }
  }
  if (pc == 0) {
    /* find the Scheme code that called out to C, by C frame pointers */
    uptr fp = (uptr)__builtin_frame_address(0);
    while (n < SAMPLER_C_DEPTH && fp >= sampler_stack_lo && fp < sampler_stack_hi - 16 && (fp & 7) == 0) {
      uptr next = ((uptr *)fp)[0], r = ((uptr *)fp)[1];
      if (sampler_code_addr(r)) { pc = r; break; }
      if (next <= fp) break;
      fp = next; n++;
    }
    sfp = (uptr)SFP(tc);
    if (pc == 0 && sampler_heap_addr((uptr)CP(tc)) && Scodep(CP(tc))) pc = (uptr)CODEENTRYPOINT(CP(tc));
    if (pc == 0) { fprintf(stderr, "no Scheme caller found on the C stack\n"); return; }
  }
  sampler_busy = 1;
  d = sampler_walk(tc, pc, sfp, Sfalse, 0, 0, &why);
  for (i = 0; i < d; i++) {
    U32 o = sampler_frames[i];
    fprintf(stderr, "#%-3d %.*s\n", i, o ? (int)(unsigned char)sampler_pool[o] : 1, o ? sampler_pool + o + 1 : "?");
  }
  fprintf(stderr, "(%d Scheme frames; walk ended: %s)\n", d, why >= 0 && why < end_samples ? ends[why] : "?");
  sampler_busy = 0;
}

void S_sampler_print_stack(void) { S_sampler_print_stack_at(0, 0); }

static void sampler_record(int depth) {
  uptr at, i;
  if (depth <= 0) return;
  at = __atomic_fetch_add(&sampler_buf_used, (uptr)depth + 1, __ATOMIC_RELAXED);
  if (at + depth + 1 > sampler_buf_words) { __atomic_fetch_add(&sampler_dropped, 1, __ATOMIC_RELAXED); return; }
  /* frames were collected innermost first; store outermost first */
  for (i = 0; i < (uptr)depth; i++) sampler_buf[at + 1 + i] = sampler_frames[depth - 1 - i];
  __atomic_store_n(&sampler_buf[at], (U32)depth, __ATOMIC_RELEASE);
}

static void sampler_handler(int sig, siginfo_t *info, void *vuc) {
  ucontext_t *uc = (ucontext_t *)vuc;
  uptr pc = SAMPLER_PC(uc);
  int depth = 0, saved_errno = errno, why = end_root;
  ptr tc = get_thread_context();
  (void)sig;

  if (!sampler_on) return;
  if (info->si_code == SI_TIMER && sampler_perf_fd >= 0) {
    /* the watchdog */
    if (sampler_perf_hits == sampler_watchdog_last) {
      ioctl(sampler_perf_fd, PERF_EVENT_IOC_REFRESH, 1);
      __atomic_fetch_add(&sampler_rearms, 1, __ATOMIC_RELAXED);
    }
    sampler_watchdog_last = sampler_perf_hits;
    errno = saved_errno;
    return;
  }
  sampler_perf_hits++;
  __atomic_fetch_add(&sampler_active, 1, __ATOMIC_ACQ_REL);
  if (!sampler_on) { __atomic_fetch_sub(&sampler_active, 1, __ATOMIC_RELEASE); return; }
  if (sampler_busy) {
    __atomic_fetch_sub(&sampler_active, 1, __ATOMIC_RELEASE);
    if (sampler_perf_fd >= 0) ioctl(sampler_perf_fd, PERF_EVENT_IOC_REFRESH, 1);
    return;
  }
  if (sampler_prefix_thread) {
    char b[24]; int n = snprintf(b, sizeof(b), "thread-%d", sampler_tid_index);
    sampler_frames[depth++] = sampler_intern(b, n);
  }

  if (sampler_code_addr(pc)) {
    if (tc != NULL && SAMPLER_TC(uc) == tc) {
      int d0 = depth;
      ptr co = sampler_code_at(pc, SAMPLER_CP(uc));
      uptr pending = 0;
      if (co != NULL) {
        pending = sampler_pending_ret(uc, pc, (uptr)CODEENTRYPOINT(co) + CODELEN(co));
        /* it must be a return point in this same code object */
        if (pending != 0 && !(sampler_code_contains(co, pending) && sampler_ret_code(pending) == co)) pending = 0;
      }
      depth = sampler_walk(tc, pc, SAMPLER_SFP(uc), SAMPLER_CP(uc), pending, depth, &why);
      /* at a return point the frame register still points at the callee's
         frame, so the caller shows twice; drop the copy */
      if (depth > d0 + 1 && sampler_frames[d0] == sampler_frames[d0 + 1]
          && (pending != 0 || (why != end_bad_sfp && pc - *(uptr *)SAMPLER_SFP(uc) < 16)))
        { memmove(&sampler_frames[d0 + 1], &sampler_frames[d0 + 2], (depth - d0 - 2) * sizeof(U32)); depth--; }
    } else {
      sampler_frames[depth++] = sampler_code_name(sampler_code_at(pc, Sfalse), pc);
      why = end_bad_tc;
    }
  } else {
    /* C code: the C frames, by frame pointer, then the Scheme code that called out */
    uptr fp = SAMPLER_FP(uc), sp = SAMPLER_SP(uc), ra = 0;
    int n = 0;
    sampler_frames[depth++] = sampler_hex_name("[C]", pc);
#if defined(__aarch64__)
    /* in a leaf without a frame record, lr holds the return address */
    if (SAMPLER_LR(uc) != 0 && sampler_code_addr(SAMPLER_LR(uc))) ra = SAMPLER_LR(uc);
#endif
    if (!(sp >= sampler_stack_lo && sp < sampler_stack_hi)) fp = 0;
    while (ra == 0 && n < SAMPLER_C_DEPTH && fp >= sp && fp < sampler_stack_hi - 16 && (fp & 7) == 0) {
      uptr next = ((uptr *)fp)[0], r = ((uptr *)fp)[1];
      if (r < 4096) break;
      if (sampler_code_addr(r)) { ra = r; break; }
      sampler_frames[depth++] = sampler_hex_name("[C]", r - 1);
      n++;
      if (next <= fp) break;
      fp = next;
    }
    why = end_c_only;
    if (sampler_in_gc) {
      if (sampler_gc_depth > 0) {
        memcpy(&sampler_frames[depth], sampler_gc_frames, sampler_gc_depth * sizeof(U32));
        depth += sampler_gc_depth; why = sampler_gc_why;
      } else
        sampler_frames[depth++] = sampler_intern("[gc]", 4);
    } else if (tc != NULL) {
      /* a non-atomic foreign call saves the frame register in the thread
         context, and puts the calling code object in its cp */
      uptr sfp = (uptr)SFP(tc);
      if (ra != 0)
        depth = sampler_walk(tc, ra, sfp, Sfalse, 0, depth, &why);
      else if (sampler_heap_addr((uptr)CP(tc)) && Scodep(CP(tc)))
        depth = sampler_walk(tc, (uptr)CODEENTRYPOINT(CP(tc)), sfp, Sfalse, 0, depth, &why);
    }
  }

  /* mark stacks that did not reach the root, so they are visible */
  if (why != end_root && why != end_c_only && depth < SAMPLER_MAX_DEPTH + SAMPLER_C_DEPTH)
    sampler_frames[depth++] = sampler_intern("[truncated]", 11);
  sampler_stats[why]++;
  sampler_stats[end_samples]++;
  sampler_record(depth);
  __atomic_fetch_sub(&sampler_active, 1, __ATOMIC_RELEASE);
  if (sampler_perf_fd >= 0) ioctl(sampler_perf_fd, PERF_EVENT_IOC_REFRESH, 1);
  errno = saved_errno;
}

/* ---------------------------------------------------------------------- */
/* starting and stopping */


/* a timer on this thread's CPU time that sends SIGPROF hz times a second */
static void sampler_start_timer(long hz) {
  struct sigevent sev;
  struct itimerspec its;
  memset(&sev, 0, sizeof(sev));
  sev.sigev_notify = SIGEV_THREAD_ID;
  sev.sigev_signo = SIGPROF;
  sev.sigev_notify_thread_id = (pid_t)syscall(SYS_gettid);
  if (timer_create(CLOCK_THREAD_CPUTIME_ID, &sev, &sampler_timer) != 0) return;
  its.it_interval.tv_sec = 0;
  its.it_interval.tv_nsec = 1000000000L / hz;
  its.it_value = its.it_interval;
  timer_settime(sampler_timer, 0, &its, NULL);
  sampler_timer_on = 1;
}

static void sampler_thread_start(void) {
  pthread_attr_t attr;
  if (!sampler_on) return;
  if (pthread_getattr_np(pthread_self(), &attr) == 0) {
    void *lo; size_t size;
    if (pthread_attr_getstack(&attr, &lo, &size) == 0) {
      sampler_stack_lo = (uptr)lo; sampler_stack_hi = (uptr)lo + size;
    }
    pthread_attr_destroy(&attr);
  }
  sampler_tid_index = __atomic_fetch_add(&sampler_thread_count, 1, __ATOMIC_RELAXED);
  if (sampler_mode != 0) {
    struct perf_event_attr pe;
    memset(&pe, 0, sizeof(pe));
    pe.size = sizeof(pe);
    pe.type = sampler_mode == 2 ? PERF_TYPE_HARDWARE : PERF_TYPE_SOFTWARE;
    pe.config = sampler_mode == 2 ? PERF_COUNT_HW_CPU_CYCLES : PERF_COUNT_SW_TASK_CLOCK;
    pe.sample_period = sampler_mode == 2 ? (__u64)(3000000000ULL / sampler_hz) : (__u64)(1000000000ULL / sampler_hz);
    pe.exclude_kernel = 1; pe.exclude_hv = 1;
    pe.disabled = 1;
    pe.wakeup_events = 1;
    sampler_perf_fd = (int)syscall(SYS_perf_event_open, &pe, 0, -1, -1, 0);
    if (sampler_perf_fd >= 0) {
      struct f_owner_ex owner;
      owner.type = F_OWNER_TID; owner.pid = (pid_t)syscall(SYS_gettid);
      fcntl(sampler_perf_fd, F_SETFL, O_ASYNC);
      fcntl(sampler_perf_fd, F_SETSIG, SIGPROF);
      fcntl(sampler_perf_fd, F_SETOWN_EX, &owner);
      ioctl(sampler_perf_fd, PERF_EVENT_IOC_REFRESH, 1);
      sampler_start_timer(SAMPLER_WATCHDOG_HZ);
      return;
    }
    if (sampler_tid_index == 0 && getenv("CHEZ_SAMPLE_DEBUG"))
      fprintf(stderr, "chez sampler: perf_event_open failed (%s); using a CPU-time timer\n", strerror(errno));
    sampler_mode = 0;
  }
  sampler_start_timer(sampler_hz);
}

static void sampler_thread_stop(void) {
  if (sampler_perf_fd >= 0) {
    ioctl(sampler_perf_fd, PERF_EVENT_IOC_DISABLE, 0);
    close(sampler_perf_fd);
    sampler_perf_fd = -1;
  }
  if (sampler_timer_on) { timer_delete(sampler_timer); sampler_timer_on = 0; }
}

void S_sampler_thread_start(void) { sampler_thread_start(); }
void S_sampler_thread_stop(void) { sampler_thread_stop(); }

/* ---------------------------------------------------------------------- */
/* naming C addresses at exit, from the executable's symbol table */

typedef struct { uptr lo, hi; const char *name; } sampler_csym;
static sampler_csym *sampler_csyms;
static uptr sampler_ncsyms;

static int sampler_csym_cmp(const void *a, const void *b) {
  uptr x = ((const sampler_csym *)a)->lo, y = ((const sampler_csym *)b)->lo;
  return x < y ? -1 : x > y;
}

static void sampler_load_csyms(void) {
  int fd = open("/proc/self/exe", O_RDONLY);
  struct stat st; unsigned char *m; Elf64_Ehdr *eh; Elf64_Shdr *sh; uptr bias = 0, i;
  char exe[4096]; ssize_t exelen; FILE *maps;
  if (fd < 0) return;
  if (fstat(fd, &st) != 0) { close(fd); return; }
  m = mmap(NULL, st.st_size, PROT_READ, MAP_PRIVATE, fd, 0);
  close(fd);
  if (m == MAP_FAILED) return;
  eh = (Elf64_Ehdr *)m;
  if (memcmp(eh->e_ident, ELFMAG, SELFMAG) != 0) return;
  /* load bias for a position-independent executable: its first mapping */
  exelen = readlink("/proc/self/exe", exe, sizeof(exe) - 1);
  if (exelen > 0 && eh->e_type == ET_DYN && (maps = fopen("/proc/self/maps", "r")) != NULL) {
    char line[4352];
    exe[exelen] = 0;
    while (fgets(line, sizeof(line), maps)) {
      unsigned long lo, off; char *path = strchr(line, '/');
      if (path && sscanf(line, "%lx-%*x %*s %lx", &lo, &off) == 2 && off == 0
          && strncmp(path, exe, exelen) == 0) { bias = lo; break; }
    }
    fclose(maps);
  }
  sh = (Elf64_Shdr *)(m + eh->e_shoff);
  for (i = 0; i < eh->e_shnum; i++) {
    if (sh[i].sh_type == SHT_SYMTAB) {
      Elf64_Sym *sym = (Elf64_Sym *)(m + sh[i].sh_offset);
      const char *str = (const char *)(m + sh[sh[i].sh_link].sh_offset);
      uptr n = sh[i].sh_size / sizeof(Elf64_Sym), j;
      sampler_csyms = malloc(n * sizeof(sampler_csym));
      if (sampler_csyms == NULL) return;
      for (j = 0; j < n; j++) {
        if (ELF64_ST_TYPE(sym[j].st_info) == STT_FUNC && sym[j].st_value != 0) {
          sampler_csyms[sampler_ncsyms].lo = sym[j].st_value + bias;
          sampler_csyms[sampler_ncsyms].hi = sym[j].st_value + bias + (sym[j].st_size ? sym[j].st_size : 1);
          sampler_csyms[sampler_ncsyms].name = str + sym[j].st_name;
          sampler_ncsyms++;
        }
      }
      qsort(sampler_csyms, sampler_ncsyms, sizeof(sampler_csym), sampler_csym_cmp);
      return;
    }
  }
}

static void sampler_write_c_name(FILE *f, const char *s, int n) {
  unsigned long a; char tmp[48]; sampler_dl_info di;
  uptr lo = 0, hi;
  if (n < 6 || n >= 47) { fwrite(s, 1, n, f); return; }
  memcpy(tmp, s + 3, n - 3); tmp[n - 3] = 0;
  a = strtoul(tmp, NULL, 16);
  hi = sampler_ncsyms;
  while (lo < hi) { uptr mid = (lo + hi) / 2; if (sampler_csyms[mid].lo <= a) lo = mid + 1; else hi = mid; }
  if (lo > 0 && a < sampler_csyms[lo - 1].hi) { fprintf(f, "[C]%s", sampler_csyms[lo - 1].name); return; }
  if (dladdr((void *)a, &di) && di.dli_sname) { fprintf(f, "[C]%s", di.dli_sname); return; }
  if (dladdr((void *)a, &di) && di.dli_fname) {
    const char *b = strrchr(di.dli_fname, '/');
    fprintf(f, "[C]%s+0x%lx", b ? b + 1 : di.dli_fname, a - (unsigned long)di.dli_fbase);
    return;
  }
  fwrite(s, 1, n, f);
}

static int sampler_rec_cmp(const void *a, const void *b) {
  const U32 *x = *(U32 * const *)a, *y = *(U32 * const *)b;
  U32 n = x[0] < y[0] ? x[0] : y[0], i;
  for (i = 1; i <= n; i++) if (x[i] != y[i]) return x[i] < y[i] ? -1 : 1;
  return x[0] < y[0] ? -1 : x[0] > y[0];
}

/* write the samples so far to f as folded stacks; returns the record count */
static uptr sampler_write_to(FILE *f) {
  uptr i, nrec = 0, used; U32 **recs;
  used = sampler_buf_used < sampler_buf_words ? sampler_buf_used : sampler_buf_words;
  for (i = 0; i < used && sampler_buf[i] != 0; i += sampler_buf[i] + 1) nrec++;
  recs = malloc((nrec + 1) * sizeof(U32 *));
  if (recs == NULL) return 0;
  nrec = 0;
  for (i = 0; i < used && sampler_buf[i] != 0; i += sampler_buf[i] + 1) recs[nrec++] = &sampler_buf[i];
  qsort(recs, nrec, sizeof(U32 *), sampler_rec_cmp);
  if (sampler_csyms == NULL) sampler_load_csyms();
  for (i = 0; i < nrec; ) {
    uptr j = i + 1, k;
    while (j < nrec && sampler_rec_cmp(&recs[i], &recs[j]) == 0) j++;
    for (k = 1; k <= recs[i][0]; k++) {
      U32 o = recs[i][k];
      const char *s = sampler_pool + o + 1; int n = (unsigned char)sampler_pool[o];
      if (k > 1) fputc(';', f);
      if (o == 0) fputs("?", f);
      else if (n > 3 && memcmp(s, "[C]", 3) == 0) sampler_write_c_name(f, s, n);
      else fwrite(s, 1, n, f);
    }
    fprintf(f, " %lu\n", (unsigned long)(j - i));
    i = j;
  }
  free(recs);
  return nrec;
}

/* wait for handlers that started before sampling stopped */
static void sampler_quiesce(void) {
  int spins = 0;
  while (__atomic_load_n(&sampler_active, __ATOMIC_ACQUIRE) != 0 && spins++ < 1000000)
    __atomic_signal_fence(__ATOMIC_SEQ_CST);
}

static void sampler_write(void) {
  FILE *f; uptr nrec;
  if (sampler_buf == NULL || sampler_path == NULL) return;
  sampler_on = 0;
  sampler_thread_stop();
  sampler_quiesce();
  f = fopen(sampler_path, "w");
  if (f == NULL) { perror(sampler_path); return; }
  nrec = sampler_write_to(f);
  fclose(f);
  if (sampler_dropped) fprintf(stderr, "chez sampler: buffer full, %lu samples dropped\n", (unsigned long)sampler_dropped);
  if (getenv("CHEZ_SAMPLE_DEBUG"))
    fprintf(stderr, "chez sampler: %s at %ld Hz, %lu samples (%lu records), %d threads; ends: root %lu, bad-ret %lu, bad-sfp %lu, foreign-tc %lu, depth %lu, c-only %lu; metacontinuation frames %lu; event re-armed %lu times\n",
            sampler_mode == 0 ? "cpu timer" : sampler_mode == 1 ? "task-clock" : "cycles", sampler_hz,
            (unsigned long)sampler_stats[end_samples], (unsigned long)nrec, sampler_thread_count,
            (unsigned long)sampler_stats[end_root], (unsigned long)sampler_stats[end_bad_ret],
            (unsigned long)sampler_stats[end_bad_sfp], (unsigned long)sampler_stats[end_bad_tc],
            (unsigned long)sampler_stats[end_depth], (unsigned long)sampler_stats[end_c_only],
            (unsigned long)sampler_stats[end_metak], (unsigned long)sampler_rearms);
}

/* the buffers and the signal handler, once */
static IBOOL sampler_setup(void) {
  const char *ev = getenv("CHEZ_SAMPLE_EVENT"), *mark = getenv("CHEZ_SAMPLE_MARK");
  const char *srcloc = getenv("CHEZ_SAMPLE_SRCLOC");
  struct sigaction sa;

  if (sampler_buf != NULL) return 1;
  sampler_prefix_thread = getenv("CHEZ_SAMPLE_THREADS") != NULL;
  sampler_debug = getenv("CHEZ_SAMPLE_DEBUG") != NULL;
  sampler_mark = !(mark != NULL && strcmp(mark, "0") == 0);
  sampler_srcloc = srcloc == NULL ? 1 : strcmp(srcloc, "0") == 0 ? 0 : strcmp(srcloc, "full") == 0 ? 2 : 1;
  sampler_mode = ev == NULL || strcmp(ev, "task-clock") == 0 ? 1 : strcmp(ev, "cycles") == 0 ? 2 : 0;
  sampler_buf_words = (uptr)256 << 20;
  sampler_buf = mmap(NULL, sampler_buf_words * sizeof(U32), PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_ANONYMOUS|MAP_NORESERVE, -1, 0);
  sampler_pool_size = (uptr)256 << 20;
  sampler_pool = mmap(NULL, sampler_pool_size, PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_ANONYMOUS|MAP_NORESERVE, -1, 0);
  sampler_slots = mmap(NULL, SAMPLER_NSLOTS * sizeof(U64), PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_ANONYMOUS|MAP_NORESERVE, -1, 0);
  if (sampler_buf == MAP_FAILED || sampler_pool == MAP_FAILED || sampler_slots == MAP_FAILED) { sampler_buf = NULL; return 0; }

  memset(&sa, 0, sizeof(sa));
  sa.sa_sigaction = sampler_handler;
  sa.sa_flags = SA_SIGINFO | SA_RESTART;
  sigemptyset(&sa.sa_mask);
  sigaction(SIGPROF, &sa, NULL);
  return 1;
}

/* mark: frame origin marks on or off; srcloc: 0 none, 1 file:line, 2 full */
static void s_sampler_config(int mark, int srcloc) {
  sampler_setup();
  sampler_mark = mark != 0;
  sampler_srcloc = srcloc < 0 ? 0 : srcloc > 2 ? 2 : srcloc;
}

static int s_sampler_start(int hz) {
  if (!sampler_setup()) return -1;
  if (sampler_on) return sampler_mode;
  sampler_hz = (hz > 0 && hz <= 100000) ? hz : 999;
  sampler_on = 1;
  sampler_thread_start();
  return sampler_mode;
}

static void s_sampler_stop(void) {
  if (!sampler_on) return;
  sampler_on = 0;
  sampler_thread_stop();
  sampler_quiesce();
}

static ptr s_sampler_take(void) {
  char *text = NULL; size_t len = 0; FILE *f; ptr bv;
  int was_on = sampler_on;
  if (sampler_buf == NULL) return Sfalse;
  if (was_on) { sampler_on = 0; sampler_quiesce(); }
  f = open_memstream(&text, &len);
  if (f == NULL) { sampler_on = was_on; return Sfalse; }
  sampler_write_to(f);
  fclose(f);
  /* clear the buffer: records end at the first zero count */
  memset(sampler_buf, 0, (sampler_buf_used < sampler_buf_words ? sampler_buf_used : sampler_buf_words) * sizeof(U32));
  sampler_buf_used = 0; sampler_dropped = 0;
  memset(sampler_stats, 0, sizeof(sampler_stats));
  sampler_on = was_on;
  bv = S_bytevector(len);
  memcpy(&BVIT(bv, 0), text, len);
  free(text);
  return bv;
}

void S_sampler_foreign_init(void) {
  Sforeign_symbol("(cs)sampler_start", (void *)s_sampler_start);
  Sforeign_symbol("(cs)sampler_stop", (void *)s_sampler_stop);
  Sforeign_symbol("(cs)sampler_take", (void *)s_sampler_take);
  Sforeign_symbol("(cs)sampler_config", (void *)s_sampler_config);
}

static void S_sampler_init(void) {
  const char *path = getenv("CHEZ_SAMPLE_STACKS"), *hz_s = getenv("CHEZ_SAMPLE_HZ");

  if (path == NULL || *path == 0 || sampler_buf != NULL) return;
  if (!sampler_setup()) return;
  sampler_hz = hz_s ? atol(hz_s) : 999;
  if (sampler_hz <= 0 || sampler_hz > 100000) sampler_hz = 999;
  sampler_path = path;
  atexit(sampler_write);
  sampler_on = 1;
  sampler_thread_start();
}

#else
static int s_sampler_start(int hz) { (void)hz; return -1; }
static void s_sampler_stop(void) { }
static ptr s_sampler_take(void) { return Sfalse; }
static void s_sampler_config(int mark, int srcloc) { (void)mark; (void)srcloc; }
static void S_sampler_init(void) { }
void S_sampler_foreign_init(void) {
  Sforeign_symbol("(cs)sampler_start", (void *)s_sampler_start);
  Sforeign_symbol("(cs)sampler_stop", (void *)s_sampler_stop);
  Sforeign_symbol("(cs)sampler_take", (void *)s_sampler_take);
  Sforeign_symbol("(cs)sampler_config", (void *)s_sampler_config);
}
void S_sampler_thread_start(void) { }
void S_sampler_thread_stop(void) { }
void S_sampler_gc_begin(void) { }
void S_sampler_gc_end(void) { }
void S_sampler_print_stack_at(uptr pc, uptr sfp) { (void)pc; (void)sfp; }
void S_sampler_print_stack(void) { }
#endif
