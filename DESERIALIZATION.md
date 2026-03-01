# Code Serialization and Deserialization in Chez Scheme

## Table of Contents

1. [Overview](#1-overview)
2. [The Two Serialization Formats](#2-the-two-serialization-formats)
3. [Boot File Structure and Loading Sequence](#3-boot-file-structure-and-loading-sequence)
4. [The vfasl Loading Process Step by Step](#4-the-vfasl-loading-process-step-by-step)
5. [Code Object Layout and Relocation](#5-code-object-layout-and-relocation)
6. [GC Interaction with Code Objects](#6-gc-interaction-with-code-objects)
7. [Memory Management](#7-memory-management)
8. [Backend Characterization](#8-backend-characterization)
9. [Optimization Proposals](#9-optimization-proposals)

---

## 1. Overview

When Chez Scheme starts, it must load its runtime—all the compiler, expander,
library management, I/O system, and other infrastructure—from boot files on
disk into a running heap. This is a cold-start deserialization problem:
approximately 11MB of compressed data (petite.boot ~6.6MB + scheme.boot ~4.7MB)
must be decoded, allocated into the garbage-collected heap, and have all
internal pointers fixed up so they point to valid memory addresses.

The deserialization process is inherently O(n) in the size of the data: every
pointer in the loaded objects must be examined and adjusted. This document
explains exactly how that process works, what makes it expensive, and proposes
concrete strategies for making it faster.

The central tension is this: Scheme objects contain tagged pointers that encode
absolute memory addresses. A serialized file doesn't know where in memory its
objects will land, so every pointer must be fixed up at load time. The
question is whether we can reduce or eliminate that fixup work.

---

## 2. The Two Serialization Formats

Chez Scheme has two serialization formats. Both can appear inside boot files.

### 2.1 FASL (Fast Load)

**Writer:** `s/fasl.ss`
**Reader:** `c/fasl.c`, function `faslin()`

FASL is a tree-walking serialization format with graph sharing. It represents
Scheme objects as a stream of tagged bytes:

```
<fasl-file>   -> <fasl-group>*
<fasl-group>  -> <fasl-header> <fasl-object>*
<fasl-header> -> {header}\0\0\0chez <uptr version> <uptr machine-type> (<deps>...)
<fasl-object> -> <situation> <uptr size> <pcfasl>
<pcfasl>      -> <compressed> <uptr uncompressed-size> <compressed fasl>
               | {uncompressed} <fasl>
```

Integers use a variable-length encoding (7 bits per byte with a continuation
bit in the low-order position, `c/fasl.c:156-167`). Each object is prefixed by
a type tag. Shared structure is handled via graph nodes: `fasl-type-graph`
establishes a sharing table, `fasl-type-graph-def` stores an object at an
index, and `fasl-type-graph-ref` references it later.

The FASL reader (`faslin()`) is a recursive function that allocates objects on
the fly. For code objects, it reads the raw machine code bytes, builds a
relocation table, and then calls `s_link_code_object()` to patch all the
code's internal references.

FASL is general-purpose and handles cross-platform serialization (e.g.,
cross-compiling for a different machine type). However, it is relatively slow
because every object must be individually parsed, allocated, and linked.

### 2.2 vfasl (Very Fast Load)

**Writer:** `s/vfasl.ss`
**Reader:** `c/vfasl.c`, function `S_vfasl()`

vfasl is an optimized format designed to be as close to a memory image as
possible. Instead of a tree of tagged objects, vfasl stores a pre-organized
blob of data that is almost ready to use as-is—it just needs pointer fixups.

The format (`c/vfasl.c:19-52`):

```
[vfasl_header]               -- fixed-size header with sizes and counts
 _
/  [symbol] ...               -> space_symbol
|  [rtd] ...                  -> space_pure
|  [closure] ...              -> space_pure
|  [impure] ...               -> space_impure
|  [pure_typed] ...           -> space_pure_typed
|  [impure_record] ...        -> space_impure_record
|  [code] ...                 -> space_code
|  [data] ...                 -> space_data
\_ [reloc] ...                -> (discarded for static generation)
 _
/  [symbol reference offsets]
|  [rtd reference offsets]
|  [singleton reference offsets]
\_ [bitmap of pointers to relocate]
```

The data section is divided into **vspaces** (`s/cmacros.ss:2275-2287`), each
corresponding to a GC allocation space. Objects within each vspace are laid
out exactly as they would appear in the heap, with one exception: all pointers
are stored as offsets from the beginning of the data section rather than
absolute addresses.

The table section contains metadata needed for fixup:
- **Symbol references**: offsets within the data where a symbol pointer needs
  to be replaced with an interned symbol
- **RTD references**: offsets where a record type descriptor needs interning
- **Singleton references**: offsets where sentinel values need replacement
  with actual singletons (empty string, empty vector, etc.)
- **Pointer bitmap**: one bit per pointer-sized word, indicating which words
  contain pointers that need offset→address conversion

The vfasl header (`s/cmacros.ss:2291-2302`) contains:
- `data-size`: total size of the data section
- `table-size`: total size of the table section
- `result-offset`: offset of the "result" value in the data
- `vspace-rel-offsets`: starting offset of each vspace (relative to data start)
- `symref-count`, `rtdref-count`, `singletonref-count`: counts for each table

---

## 3. Boot File Structure and Loading Sequence

### 3.1 Boot File Format

Boot files use the same container format as compiled `.so` files. The file
is a sequence of fasl groups, each starting with the header
`\0\0\0chez<version><machine-type>(<dependencies>...)`, followed by
fasl objects tagged with a "situation" (visit, revisit, or visit-revisit).

Each fasl object can contain either traditional FASL data or vfasl data,
and may be compressed with gzip or LZ4.

### 3.2 The Loading Sequence

Boot loading is orchestrated by `Sbuild_heap()` in `c/scheme.c:1156`.

**Step 1: Initialization** (`c/scheme.c:1175-1236`)
```
S_boot_time = 1
main_init()               -- initializes all subsystems (segments, GC, intern, etc.)
S_vfasl_boot_mode = 1     -- subsequent loads go to static generation
```

**Step 2: Load base boot file** (`c/scheme.c:928-944`)

The `load()` function reads the first (base) boot file. The first three
objects are special:
1. `error_invoke_code_object` — the error handler trampoline
2. `invoke_code_object` — the normal code invocation trampoline
3. `base_rtd` — the root record type descriptor

**Step 3: Load remaining objects** (`c/scheme.c:949-961`)

Each remaining object is processed by `boot_element()` (`c/scheme.c:894-908`):
- If it's a **procedure**: call it immediately (this runs boot code)
- If `load_binary` is set: pass it to the load-binary handler
- If it's a **vector**: recursively process each element

This is critical: **boot code runs between deserialization calls**. Each
vfasl block is loaded and fixed up, and the resulting procedures are
executed. These procedures may intern symbols, define record types, install
library entries, etc. This interleaving of load and execution constrains
optimization strategies.

**Step 4: Load additional boot files** (`c/scheme.c:1243-1247`)

After the base boot, additional boot files (e.g., `scheme.boot` after
`petite.boot`) are loaded the same way, but without the special base-rtd
handling.

**Step 5: Final compaction** (`c/scheme.c:1249-1251`)
```
Scompact_heap()           -- full GC to static generation
S_vfasl_boot_mode = 0
```

### 3.3 The Scompact_heap() Between Blocks

During boot loading, when `S_vfasl_boot_mode` is set and a vfasl block
is encountered, `Scompact_heap()` is called _before_ loading each block
(`c/fasl.c:449-452`):

```c
if ((kind == fasl_type_vfasl) && S_vfasl_boot_mode) {
    Scompact_heap();  // full collection to static generation
}
```

`Scompact_heap()` (`c/gcwrapper.c:482`) triggers a full garbage collection
that promotes all objects to the static generation. This is done because
previously-loaded boot code may have interned symbols or created objects
that need to be in static generation before the next block is loaded.

This per-block compaction is one of the more expensive aspects of boot
loading and a target for optimization.

---

## 4. The vfasl Loading Process Step by Step

The function `S_vfasl()` in `c/vfasl.c:92-461` performs the following passes:

### Pass 1: Header Parsing (lines 109-127)

Read the fixed-size vfasl header. Extract sizes for each vspace and the
table section. Compute vspace offset boundaries.

### Pass 2: Space Allocation and Data Copy (lines 132-165)

For each vspace with non-zero size:
```c
find_room(tc, vspace_spaces[s],
          (to_static ? static_generation : 0),
          type_untyped, sz, vspaces[s]);
```
Then copy data in: either `memcpy` from a bytevector or `S_fasl_bytesin()`
from a stream. On `CANNOT_READ_DIRECTLY_INTO_CODE` platforms (Apple), code
is first read to a temporary buffer, then memcpy'd to the code space.

This is the most expensive single operation: reading and copying ~11MB of
data into freshly allocated heap segments.

### Pass 3: Pointer Bitmap Fixup (lines 229-255)

Walk the bitmap one byte at a time. For each set bit, the corresponding
pointer-sized word in the data is an offset that must be converted to an
actual address:

```c
while (bm != bm_end) {
    octet m = *bm;
    // For each bit 0..7:
    if (m & (1 << i)) {
        ptr *p = SPACE_PTR(p_off);
        *p = find_pointer_from_offset((uptr)*p, vspaces, vspace_offsets);
    }
    p_off += sizeof(uptr);
    bm++;
}
```

`find_pointer_from_offset()` (`c/vfasl.c:579-589`) converts a data-relative
offset (with type tag) to an absolute pointer by finding which vspace the
offset falls into:

```c
static ptr find_pointer_from_offset(uptr p_off, ptr *vspaces, uptr *vspace_offsets) {
    int s = 0;
    ITYPE t = TYPEBITS(p_off);
    p_off = (uptr)UNTYPE(p_off, t);
    while (p_off >= vspace_offsets[s+1])
        s++;
    return TYPE(ptr_add(vspaces[s], p_off - vspace_offsets[s]), t);
}
```

The inner `while` loop makes this slightly worse than a single add per
pointer, since it scans through vspace boundaries.

### Pass 4: Singleton Replacement (lines 260-271)

Replace sentinel values with actual singleton objects (empty string, empty
vector, empty bytevector, etc.). Uses a table of offsets into the data
(`singletonrefs`). Small number of entries.

### Pass 5: Symbol Interning (lines 273-330)

Walk the symbol vspace. For each symbol object:
1. Initialize its value to `sunbound` and code to `nonprocedure_code`
2. Call `S_intern4()` to look up/insert in the global symbol table
3. If the symbol already exists (already interned), record the existing
   symbol in the value slot for later replacement

This pass acquires `tc_mutex` (thread safety) and involves hash table
lookups with string comparisons—relatively expensive per symbol.

### Pass 6: Symbol Reference Replacement (lines 332-348)

Walk the symbol reference table. For each reference offset, find the
corresponding symbol in the symbol vspace and, if it was replaced by an
already-interned symbol, update the pointer.

### Pass 7: RTD Interning (lines 351-395)

Walk the RTD (record type descriptor) vspace. For each RTD:
1. Fix up its meta-type and parent references
2. Call `S_fasl_intern_rtd()` to check for an existing RTD with the same UID
3. If a conflicting RTD exists, record the replacement

This also requires `tc_mutex`.

### Pass 8: RTD Reference Replacement (lines 397-414)

Walk the RTD reference table. Replace RTD pointers with their interned
versions where applicable.

### Pass 9: Closure Code Pointer Fixup (lines 416-435)

Walk the closure vspace. Each closure contains a pointer to its code object,
stored as an offset. Add the delta between the code vspace's actual address
and its file offset:

```c
uptr code_delta = (uptr)ptr_subtract(vspaces[vspace_code], vspace_offsets[vspace_code]);
while (cl != end_closures) {
    ptr code = CLOSCODE(cl);
    code = ptr_add(code, code_delta);
    SETCLOSCODE(cl, code);
    cl = ptr_add(cl, size_closure(CLOSLEN(cl)));
}
```

### Pass 10: Code Relinking (lines 437-577)

This is the most complex pass. For each code object in the code vspace:

1. Locate its relocation table (stored in the reloc vspace, referenced by
   offset from the code object)
2. If loading to static generation and not retaining relocations, either
   discard the reloc table or copy it to a permanent location
3. Walk the relocation table entries. For each entry:
   a. Extract the type, code offset, and item offset
   b. The "object" is stored as a compact value in place of the instruction's
      constant field (read via `memcpy` of an I32 from the code)
   c. Decode the object: it may be a C entry, library entry, symbol, singleton,
      or a pointer into the vfasl data
   d. Call `S_set_code_obj()` to patch the instruction at the specified offset

The `relink_code()` function (`c/vfasl.c:480-577`) handles the vfasl-specific
encoding where objects referenced by code relocations are stored as tagged
fixnums with a `vfasl_reloc_tag` indicating the type of reference:
- `vfasl_reloc_c_entry_tag`: C runtime entry point
- `vfasl_reloc_library_entry_tag`: library entry (closure)
- `vfasl_reloc_library_entry_code_tag`: library entry (code pointer)
- `vfasl_reloc_symbol_tag`: interned symbol
- `vfasl_reloc_singleton_tag`: singleton object

### Summary of Costs

| Pass | What it does | Complexity | Dominant cost |
|------|-------------|------------|---------------|
| 2 | Data copy | O(n) bytes | Memory bandwidth |
| 3 | Pointer fixup | O(n/ptr_size) | `find_pointer_from_offset` per pointer |
| 5 | Symbol intern | O(num_symbols) | Hash lookups, string compares |
| 10 | Code relink | O(num_relocs) | `S_set_code_obj` per relocation |
| Others | Reference replacement | O(num_refs) | Smaller contribution |

---

## 5. Code Object Layout and Relocation

### 5.1 Code Object Structure

A code object has a 64-byte header (`header_size_code = 0x40`), typed as
`type_code = 0xBE`, followed by the raw machine code bytes starting at
offset 0x41 (`code_data_disp`).

Header fields (from `s/mkgc.ss:571-586`):
- `code-type`: type field with flags byte
- `code-length`: size in bytes of the executable code
- `code-reloc`: pointer to the relocation table (or NULL if discarded)
- `code-name`: symbol or string identifying the function
- `code-arity-mask`: bitmask encoding accepted argument counts
- `code-closure-length`: number of free variables (CODEFREE)
- `code-info`: debug/inspector information record
- `code-pinfo*`: profiling information

Code flags (`boot/pb/equates.h`):
- `code_flag_system` (0x1), `code_flag_continuation` (0x2),
  `code_flag_template` (0x4), `code_flag_guardian` (0x8),
  `code_flag_mutable_closure` (0x10), `code_flag_arity_in_closure` (0x20),
  `code_flag_single_valued` (0x40), `code_flag_lift_barrier` (0x80)

### 5.2 Relocation Table Structure

The relocation table is a separate untyped object (`type_untyped`) with a
16-byte header (`header_size_reloc_table = 0x10`):
- `reloc-table-size` at offset 0x0: number of uptr entries
- `reloc-table-code` at offset 0x8: back-pointer to the code object
- `reloc-table-data` at offset 0x10: array of uptr entries

Each relocation entry can be in short or extended format:

**Short format** (1 uptr):
- Bits 0: extended format flag (0)
- Bits 1: has item offset flag
- Bits 2+: relocation type
- Plus packed code_offset (26 bits) and item_offset (26 bits)

**Extended format** (3 uptrs):
- Entry 0: type with extended flag set (bit 0 = 1)
- Entry 1: full item_offset
- Entry 2: full code_offset

The code_offset values are **delta-encoded**: each offset is relative to
the previous relocation's position, and they accumulate (`a += code_off`).

### 5.3 Relocation Processing

`S_set_code_obj()` (`c/fasl.c:1431-1542`) writes a pointer value into the
machine code at a specific offset. The exact mechanism is architecture-specific:

**reloc_abs** (all platforms):
```c
STORE_UNALIGNED_UPTR(address, item);  // raw pointer store
```

**Portable bytecode** (`reloc_pb_abs`, `reloc_pb_proc`):
```c
// pb_set_abs just stores an unaligned uptr (c/fasl.c:1646-1648)
STORE_UNALIGNED_UPTR(address, item);
```
pb is the simplest: constants in the instruction stream are just raw pointer
values, no instruction encoding to worry about.

**x86_64** (`reloc_x86_64_jump`, `reloc_x86_64_call`):
```c
// x86_64_set_jump (c/fasl.c:1813-1833)
I64 disp = (I64)item - ((I64)address + 5);
if ((I32)disp == disp) {
    // Short form: 5-byte call/jmp with 32-bit displacement + 7-byte nop
} else {
    // Long form: MOV imm64 to RAX (10 bytes) + CALL/JMP RAX (2 bytes)
}
```
x86_64 has two instruction encodings depending on whether the target fits
in a 32-bit PC-relative displacement. Prefers short form for performance.

**ARM64** (`reloc_arm64_abs`, `reloc_arm64_jump`, `reloc_arm64_call`):
```c
// arm64_set_abs (c/fasl.c:1726-1735)
// Uses 4 instructions to load a 64-bit immediate:
//   MOVZ  Xd, #imm16          (bits 0-15)
//   MOVK  Xd, #imm16, LSL 16  (bits 16-31)
//   MOVK  Xd, #imm16, LSL 32  (bits 32-47)
//   MOVK  Xd, #imm16, LSL 48  (bits 48-63)
```
ARM64 loads 64-bit constants by patching immediate fields across four 32-bit
instructions. All three relocation types (abs/jump/call) use the same encoding.

The inverse function `S_get_code_obj()` (`c/fasl.c:1544-1642`) reads the
current pointer value back out of the instruction stream. This is used by
the GC during sweeping.

---

## 6. GC Interaction with Code Objects

### 6.1 Sweep During Collection

Code objects live in `space_code`. During garbage collection, the generated
`sweep_code_object()` function (defined in `s/mkgc.ss:571-586,1112-1177`)
processes each code object:

1. Trace the non-self header fields: `code-name`, `code-arity-mask`,
   `code-info`, `code-pinfo*`
2. Walk the relocation table (the `trace-code` macro, `s/mkgc.ss:1112`):
   - For each entry, call `S_get_code_obj()` to read the referenced object
   - Trace (relocate) that object
   - Call `S_set_code_obj()` to write the updated pointer back

This means the GC's code sweeping has the same O(relocs) cost as the initial
loading. For static generation code, this cost is paid only once (during the
compaction that promotes to static), then the relocation table is discarded.

### 6.2 Static Generation and Relocation Table Discarding

When a code object is promoted to the static generation (`s/mkgc.ss:1150-1155`):

```scheme
(cond
  [(&& (== from_g static_generation)
       (&& (! S_G.retain_static_relocation)
           (== 0 (& (code-type _) (<< code_flag_template code_flags_offset)))))
   (set! (code-reloc _) (cast ptr 0))]   ;; discard relocation table
  [else
   ;; keep relocation table, update back-pointer
   ])
```

If a code object is in static generation, not flagged as a template, and
`retain_static_relocation` is not set, the relocation table pointer is set
to NULL. This means the GC will never trace through this code object's
relocations again—its references are permanently frozen.

This is significant for mmap: boot code objects end up in static generation
with no relocation tables. Their relocation information is needed only during
the initial loading process and is then thrown away.

### 6.3 W^X Handling

On platforms with W^X (Write XOR Execute) restrictions (primarily Apple ARM64),
code memory cannot be simultaneously writable and executable. The system uses:

- `S_thread_start_code_write()` / `S_thread_end_code_write()` to bracket
  code modifications
- `pthread_jit_write_protect_np()` to toggle between write and execute modes
- `MAP_JIT` flag when allocating code memory
- `CANNOT_READ_DIRECTLY_INTO_CODE`: data must be read into a temporary buffer
  first, then copied into code memory

---

## 7. Memory Management

### 7.1 The Segment System

Memory is organized into 64KB segments (`bytes_per_segment`). Segments are
allocated in chunks via `S_getmem()` (`c/segment.c:161-193`), which uses:
- `mmap(MAP_PRIVATE | MAP_ANONYMOUS)` on Unix
- `VirtualAlloc()` on Windows
- `malloc()` as fallback for small allocations

Each segment has a `seginfo` struct (`c/types.h:143-185`) tracking:
- `space`: which allocation space (symbol, pure, impure, code, data, etc.)
- `generation`: which GC generation (0 to static_generation=255)
- `dirty_bytes`: write barrier tracking
- `marked_mask`: GC mark bits
- `chunk`: which OS-level allocation chunk this segment belongs to

The segment table is a multi-level lookup table indexed by address, allowing
O(1) lookup of segment metadata for any heap pointer.

### 7.2 Code-Specific Allocation

Code segments are tracked separately from data segments (`S_code_chunks`
vs `S_chunks` in `c/segment.c:57-62`). On Unix, code segments are allocated
with `PROT_READ | PROT_WRITE | PROT_EXEC` (or just `PROT_WRITE | PROT_READ`
on W^X platforms where execute permission is toggled separately).

On x86_64, the allocator first tries `MAP_32BIT` to get addresses in the
lower 2GB of address space (`c/segment.c:173-186`), which enables shorter
jump instructions. It falls back to the full address space if that fails.

### 7.3 Static Generation

Static generation (generation 255) objects are never collected by the GC.
Once boot loading completes and `Scompact_heap()` is called, all boot objects
are promoted to static generation. This means:
- They are never moved
- Their memory is never freed
- No write barriers are needed for references between static objects
- Relocation tables are discarded (unless `retain_static_relocation` is set)

This makes static generation a natural fit for mmap: the memory is permanent
and the objects are immobile.

---

## 8. Backend Characterization

Different backends have fundamentally different constraints and opportunities
for deserialization optimization. This section characterizes each.

### 8.1 Portable Bytecode (pb)

**Relocation model**: Simplest possible. Only two types: `reloc_pb_abs` and
`reloc_pb_proc`. Both are implemented identically as a raw unaligned pointer
store (`STORE_UNALIGNED_UPTR`).

**Code permissions**: No execute permission needed. `S_PROT_CODE` is defined
as `PROT_WRITE | PROT_READ` (`c/version.h:158-159`). This means code pages
can be mmapped from a file without any special permission dance.

**Instruction cache**: No coherence issues. The pb interpreter reads code as
data, so there's no instruction cache to invalidate.

**Implication**: pb is the easiest backend for mmap optimization. Code pages
could potentially be mmapped read-only if relocations are eliminated.
The uniform, simple relocation model makes position-independent schemes
more feasible.

### 8.2 x86_64 Linux

**Relocation model**: Three types. `reloc_abs` (raw pointer store),
`reloc_x86_64_jump` and `reloc_x86_64_call` (which encode either a 5-byte
`call/jmp rel32` + 7-byte NOP for short displacements, or a 10-byte
`MOV imm64, RAX` + 2-byte `CALL/JMP RAX` for long ones). Plus
`reloc_x86_64_popcount` (special case).

**Code permissions**: Pages are `PROT_READ | PROT_WRITE | PROT_EXEC`.
No W^X restrictions on Linux. Can mmap with full permissions.

**Instruction cache**: x86 has coherent instruction and data caches. No
explicit cache flush needed after modifying code. (`S_doflush()` is a no-op
on x86.)

**Address preference**: Prefers `MAP_32BIT` for code allocations to enable
short jump instructions. This means code at arbitrary file-backed mmap
addresses (which may be outside the low 2GB) could cause the 12-byte long
form to be used instead of the 5-byte short form. This is a correctness
concern, not just performance: both forms are supported, but the code
generator emits 12-byte slots to accommodate either.

**Implication**: Good candidate for mmap. Main concern is that file-backed
mmap addresses may not be in the low 2GB, but this only affects performance
(long-form jumps), not correctness. No cache flush needed.

### 8.3 ARM64 macOS

**Relocation model**: Three types that are all handled identically:
`reloc_arm64_abs`, `reloc_arm64_jump`, `reloc_arm64_call` all call
`arm64_set_abs()` which patches four 32-bit instructions (MOVZ + 3x MOVK)
to load a 64-bit immediate.

**Code permissions**: W^X enforced. `WRITE_XOR_EXECUTE_CODE` is defined.
Code pages cannot be simultaneously writable and executable.
`CANNOT_READ_DIRECTLY_INTO_CODE` is defined: data must be read to a temporary
buffer, then copied to code memory.

**Memory mapping**: Code allocations use `MAP_JIT` flag. Write access requires
calling `pthread_jit_write_protect_np(false)` before writing and
`pthread_jit_write_protect_np(true)` after.

**Instruction cache**: Requires explicit invalidation after code modification
via `S_doflush()` → `sys_icache_invalidate()`.

**Implication**: Most constrained backend for mmap. Cannot directly mmap a
file as executable code. The W^X model means:
1. File data must be read into writable memory
2. Fixups applied while writable
3. Memory made executable (and no longer writable)

For non-code vspaces (symbols, closures, data, etc.), mmap is
straightforward—only the code vspace has W^X constraints. A practical
approach might mmap non-code data directly but handle code space separately.

---

## 9. Optimization Proposals

### 9.1 Eliminate Per-Block Scompact_heap (All Backends)

**Current behavior**: Every time a vfasl block is encountered during boot
loading, `Scompact_heap()` is called first (`c/fasl.c:449-452`). This is a
full garbage collection that promotes everything to static generation.

**Why it exists**: Running boot code between blocks can intern symbols,
create objects, etc. The compaction ensures these are in static generation
before the next block's symbols are interned (to avoid generation
inconsistencies).

**Proposal**: Investigate whether this compaction can be deferred or batched.
Options:
- Only compact when actually necessary (when symbols have been interned since
  the last compaction)
- Batch multiple vfasl blocks and compact once
- Use a generation-aware symbol intern that handles cross-generation references

**Risk**: Low. The compaction is defensive, and its exact necessity should be
verified.

**Impact**: Potentially significant. Full GC collection is expensive, and
this is called O(blocks) times during boot.

### 9.2 Copy-on-Write mmap (All Backends, Easiest Win)

**Idea**: Instead of reading the boot file sequentially into freshly
allocated heap memory, `mmap()` the vfasl data section with `MAP_PRIVATE`
and apply fixups in place.

**How it works**: `MAP_PRIVATE` gives copy-on-write semantics. The OS maps
the file pages into the process address space without copying. When a fixup
writes to a page, the OS copies just that page to anonymous memory. Pages
that are never written (e.g., pure code bytes between relocation points)
remain file-backed and shared across processes.

**Requirements**:
- Boot files must store vfasl data **uncompressed**. Currently, boot data
  is typically LZ4-compressed. An uncompressed boot file option would be
  needed (or a build-time choice).
- The vfasl data sections should be page-aligned within the boot file to
  maximize sharing.

**Per-backend considerations**:
- **pb**: Straightforward. mmap with `PROT_READ | PROT_WRITE`. No execute
  permission needed.
- **x86_64**: mmap with `PROT_READ | PROT_WRITE | PROT_EXEC`. Code can
  be executed directly from mmapped pages.
- **ARM64**: Non-code vspaces can be mmapped normally. The code vspace
  cannot be mmapped directly as executable. Options:
  - mmap the entire data section as writable, apply fixups, then
    `mprotect()` the code region. (May not work with MAP_JIT requirements.)
  - mmap non-code vspaces from file; allocate code space separately and
    memcpy + fixup the code. (Hybrid approach.)

**Integration with segment table**: The mmapped memory is at an arbitrary
address, not allocated through the chunk system. Need to register segments
for the mmapped region:
- Allocate `seginfo` structs for each segment-sized region in the mapping
- Insert them into the segment table via `expand_segment_table()`
- Set space and generation appropriately
- On unmap/shutdown, reverse the registration

**Impact**: Eliminates the sequential read of the entire boot file data.
For cold-start (file not in page cache), the OS can demand-page only the
portions actually needed. For warm-start, the file is already in page cache
and mmap avoids the extra copy to heap memory. Pages containing only pure
data (no pointer fixups) remain file-backed and shared across processes.

### 9.3 Contiguous Allocation with Delta Pointer Fixup (All Backends)

**Idea**: Instead of allocating each vspace separately (potentially at
distant memory addresses), allocate all vfasl data in one contiguous block.
Then the pointer bitmap fixup becomes a simple `*p += delta` instead of
calling `find_pointer_from_offset()`.

**Current cost**: `find_pointer_from_offset()` does:
```c
while (p_off >= vspace_offsets[s+1]) s++;
```
This loop runs up to 9 iterations (number of vspaces) per pointer. While
the branch predictor will learn the pattern, it's still more work than a
single addition.

**With contiguous allocation**: Every pointer in the vfasl data is an offset
from the base. If the data is loaded at base address B, every offset just
needs B added to it:
```c
while (bm != bm_end) {
    octet m = *bm;
    if (m & (1 << i)) {
        ptr *p = (ptr*)((uptr)base + p_off);
        *p = (ptr)((uptr)*p + delta);
    }
    p_off += sizeof(uptr);
    bm++;
}
```

**Composes with mmap**: If the boot file's data section is mmapped
contiguously, delta = mmap_address - 0 (since offsets are from 0 in the
file).

**Challenge - segment registration**: Different regions of the contiguous
block need different space tags for GC tracking. This requires registering
multiple segments with different space values within the same contiguous
mapping. This is not fundamentally difficult—each 64KB segment can be
independently tagged—but it's not how the current system works. Segments
within a chunk currently all start as "unused" and are individually
assigned spaces. A new path for externally-provided memory would be needed.

**Challenge - static generation simplification**: For static generation
objects (which is what boot data becomes), space tagging matters less
because the GC never moves or collects these objects. The space tag is
primarily needed for the GC to know how to trace the objects. Since static
objects are never traced after compaction (reloc tables discarded), the
space tag could potentially be simplified.

**Impact**: Moderate improvement to the pointer bitmap fixup pass. The
pass itself is already fairly fast (simple loop with bitmap), so the gain
is proportional to the overhead of `find_pointer_from_offset()` per pointer.
The bigger value is enabling composition with mmap.

### 9.4 Position-Independent Relocation for pb

**Idea**: On the pb backend, relocation entries store absolute addresses
via `STORE_UNALIGNED_UPTR`. Instead, store offsets relative to the code
object or a base address. This makes the code bytes themselves immutable
and mmappable without any COW.

**How pb works today**: The code generator emits a sequence of pb
instructions that load a constant. The constant slot in the instruction
stream holds a raw pointer. At load time, `relink_code()` writes the
actual pointer value into this slot via `S_set_code_obj("vfasl", ...)`.

**Position-independent approach**: Instead of patching absolute addresses
into the instruction stream, store offsets. The pb interpreter would add
a base register value when interpreting these instructions. This is
analogous to PIC (position-independent code) in native compilers.

**Advantages**:
- Code bytes never need modification after loading
- Code pages can be mmapped read-only and shared across processes
- The relocation table is no longer needed at all for non-symbol references

**Challenges**:
- Requires changes to the pb interpreter to support offset-based addressing
- Symbol and library entry references still need resolution (they're not
  at fixed offsets)
- Performance: adding a base offset on every constant load adds cycles
- The pb backend is already slower than native; adding overhead may not
  be acceptable

**Impact**: Potentially significant for pb, but the implementation
complexity is high and the performance tradeoff must be measured. Best
suited for contexts where startup time matters more than steady-state
performance.

### 9.5 Lazy Code Relinking (Primarily pb)

**Idea**: Instead of relinking every code object at boot time, leave them
unlinked and relink on first call.

**Mechanism**:
1. After loading vfasl data, skip `relink_code()` for most code objects
2. Set each unlinked closure's code pointer to a special "relinking
   trampoline"
3. When the trampoline is called, it:
   a. Saves all arguments
   b. Calls `relink_code()` for the target code object
   c. Updates the closure's code pointer to the now-linked code
   d. Jumps to the real entry point

**What must be linked eagerly**:
- `error_invoke_code_object` and `invoke_code_object` (loaded first, used
  immediately)
- Library entries (referenced by index, not through closures)
- C entries (runtime primitives)
- Code objects executed during boot (before boot loading completes)

**Per-backend considerations**:
- **pb**: Simplest. The trampoline is a pb procedure. No instruction cache
  issues. Could be implemented entirely in Scheme.
- **x86_64**: Trampoline must save registers and follow calling convention.
  No icache issues. Moderate complexity.
- **ARM64**: Trampoline needs register saving + icache invalidation after
  relinking. Most complex due to W^X constraints.

**Thread safety**: Multiple threads could call the same unlinked procedure
simultaneously. Need either:
- A lock per code object (expensive in space)
- An atomic CAS on the closure's code pointer (the trampoline checks and
  retries)
- Accept redundant relinking (idempotent operation)

**Impact**: Could significantly reduce boot time by deferring work. However,
boot loading runs a lot of code (the boot code itself), so many code objects
will be linked during boot anyway. The main benefit is for large libraries
that are loaded but rarely used in a given session (e.g., the full compiler
when only running pre-compiled code). The implementation is complex and
architecture-specific.

### 9.6 mmap Directly as Static Generation Heap (All Backends, Biggest Win)

**Idea**: Design the boot file so its data section IS the static generation
heap image. At load time, mmap it directly and register the segments,
applying only the minimal fixups needed.

This is the most ambitious proposal and offers the largest potential speedup.

**Design**:

1. **Boot file layout**: The vfasl data section is organized as a sequence
   of 64KB-aligned segments. Each segment's space tag and generation are
   recorded in a side table in the file. The data within each segment is
   laid out exactly as it would appear in the heap.

2. **At load time**:
   ```
   fd = open("petite.boot")
   data = mmap(fd, offset, size, MAP_PRIVATE, PROT_READ|PROT_WRITE)
   for each segment:
     seginfo = allocate_seginfo()
     seginfo->space = recorded_space
     seginfo->generation = static_generation
     expand_segment_table(segment_address, seginfo)
   apply_fixups(data, fixup_table)
   mprotect(code_region, PROT_READ|PROT_EXEC)  // if needed
   ```

3. **What's eliminated**:
   - Reading boot file data into a buffer: **eliminated** (mmap)
   - Allocating heap segments: **eliminated** (mmapped memory used directly)
   - Copying data into segments: **eliminated** (data is in place)
   - Decompressing data: **eliminated** (stored uncompressed)

4. **What remains**:
   - Pointer bitmap fixup (delta-based, ~O(num_pointers) additions)
   - Symbol interning and reference replacement
   - RTD interning and reference replacement
   - Code relinking (architecture-specific instruction patching)
   - Singleton replacement

5. **Segment table integration**: Need a new function
   `S_register_external_segments()` that:
   - Takes a base address, length, and per-segment space tags
   - Creates `seginfo` structs (allocated separately, not from the mapping)
   - Creates a synthetic `chunkinfo` to track the external allocation
   - Inserts into the segment table
   - Does NOT free the memory through `S_freemem()` on cleanup (needs a
     `munmap` instead)

6. **Per-backend code space handling**:
   - **pb**: mmap code space with `PROT_READ | PROT_WRITE`. After fixups,
     no permission change needed. Ideal case.
   - **x86_64**: mmap code space with `PROT_READ | PROT_WRITE | PROT_EXEC`.
     Apply code relocations in place. Done.
   - **ARM64**: Cannot mmap file as executable. Options:
     a. mmap all non-code vspaces from file. Allocate code vspace separately
        via the normal `S_getmem()` with `MAP_JIT`. Copy code data from
        file mapping. Apply relocations. Toggle W^X.
     b. Use a separate file-backed mapping for code data as a "template",
        then copy to JIT-allocated memory. The non-code data still benefits
        from direct mmap.

**Impact**: This combines the benefits of proposals 9.2, 9.3, and partially
9.5. It eliminates the data copy (the single largest cost), makes the pointer
fixup O(1) per pointer (single addition), and naturally integrates with the
static generation model. The main costs that remain are symbol/RTD interning
and code relocation patching, which are inherently unavoidable.

For the pb backend, this could reduce boot time to nearly just the
symbol/RTD interning cost plus demand-paging overhead.

For x86_64, the same applies.

For ARM64, the non-code data (which is the majority by volume—symbols,
strings, bytevectors, closures, records, vectors) benefits fully. Only the
code vspace needs the traditional allocate-and-copy path.

### 9.7 Pre-computed Symbol Hashes (All Backends)

**Idea**: Include pre-computed hash values for symbols in the vfasl format
to speed up symbol interning.

**Current cost**: `S_intern4()` computes the hash of the symbol's name
string, then probes the hash table. For the base boot file (petite.boot),
all symbols are new, so there are no collisions to resolve—but the hash
still must be computed.

**Optimization**: Store the hash in the vfasl symbol data. `S_intern4()`
can use the pre-computed hash directly instead of re-hashing.

For the base boot file, an additional optimization: since all symbols are
new (no pre-existing symbols), bulk-insert them into the hash table without
checking for duplicates. This turns the intern loop from
hash+probe+compare+insert into just hash+insert.

**Impact**: Small but measurable. Symbol interning is a serial operation
(requires mutex), so reducing per-symbol cost helps. Most valuable when
combined with other optimizations that have already eliminated the larger
costs (data copy, pointer fixup).

### 9.8 Recommended Strategy

The proposals above are ordered by implementation complexity and compose
well. Here's the recommended approach:

**Phase 1: Low-hanging fruit**
1. Investigate eliminating per-block `Scompact_heap()` (9.1)
2. Add uncompressed boot file option
3. Implement COW mmap of vfasl data (9.2)
4. Implement contiguous allocation + delta fixup (9.3)

These are relatively simple changes that provide immediate benefit on all
backends.

**Phase 2: Static generation mmap**
5. Design and implement external segment registration (9.6)
6. mmap boot file data directly as static generation
7. Handle ARM64 code space separately

This is the big architectural change that provides the largest benefit.

**Phase 3: Further optimization**
8. Pre-computed symbol hashes (9.7)
9. Lazy code relinking for non-essential code (9.5)
10. pb-specific position-independent relocations (9.4)

These are refinements on top of the mmap infrastructure.

For each phase, measurement is essential: instrument boot loading to
determine where time is actually spent, and verify that optimizations
provide the expected improvement. The distribution of time across the
fixup passes (data copy vs. pointer fixup vs. symbol intern vs. code
relink) will determine which optimizations matter most in practice.
