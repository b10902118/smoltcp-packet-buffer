# Flux on `PacketBuffer`: Initial Results, Difficulties, and Lessons

Verify a few basic invariants of `PacketBuffer` (`src/storage/packet_buffer.rs`) and the `RingBuffer` it is built on  
(`src/storage/ring_buffer.rs`) with Flux.

## 1 Invariants checked

| # | Invariant | Where it is stated |
|---|-----------|--------------------|
| I1 | Every ring is well-formed: `len <= cap`, and `read_at < cap` (or `read_at == 0` when `cap == 0`). Every slice index in `RingBuffer` is in bounds. | `#[invariant]` on `RingBuffer` |
| I2 | No `PacketBuffer` operation changes `packet_capacity()` or `payload_capacity()`. `payload_bytes_count() <= payload_capacity()`. `reset()` empties both rings. | `#[invariant]` on `PacketBuffer` plus `ensures` clauses on every `&mut self` method |
| I3 | `enqueue(size)` returns a slice of exactly `size` bytes on `Ok`, including when padding has to wrap around the end of the payload ring. | Return type `Result<&mut [u8][size], Full>` |

Result: `cargo flux` passes with 0 errors (39 functions checked, 15 trusted,
54 constraints solved).

How to run (no feature flags needed):

```
cd flux_annotations
cargo flux
```

## 2 Do the specs catch bugs? (injected-bug testing)

Each bug was injected one at a time and Flux was re-run. The bugs were first run
in the smoltcp crate and then repeated in this crate with the same results. How
each test was set up, and where Flux reports each bug, is described in
`injected_bug_tests.md`.

| Injected bug | Invariant | Caught? |
|--------------|-----------|---------|
| `enqueue` pads one byte too few before wrapping | I3 | yes* |
| `enqueue` reserves `size + 1` bytes | I3 | yes* |
| `enqueue` skips the "padding + packet still fits" check | I3 | yes* |
| `reset` forgets to clear the payload ring | I2 | yes |
| `enqueue_unallocated` allows `count <= window + 1` | I1 | yes |
| `get_unallocated` drops the end-of-storage clamp | I1 (bounds) | yes |
| `dequeue_allocated` forgets to wrap `read_at` | I1 | yes |

 Only after removing the `debug_assert!(payload_buf.len() == size)` in `enqueue`.
With the assert present, Flux missed all three. The reason is Lesson 1 below.

## 3 Difficulties and challenges

### 3.1 Tooling and setup (most of the time went here)

- **The standard-library specs are not loaded by default.** Without the `flux-core`
crate, `cmp::min`, `Option::unwrap` and slice range indexing (`s[a..b]`) are
unspecified, so most bounds facts are invisible. The `-Fstd-extern-specs` flag is
supposed to inject them, but it does not work. In smoltcp it broke on the build
script ("required to be available in rlib format"). This crate has no build
script, but the flag also applies to dependencies, and building `flux-rs` then
fails ("can't find crate for `flux_core`"). What worked: add `flux-core` as a git
dependency.
- **Version skew.** Adding `flux-core` as an unpinned git dependency moved
`flux-rs` to a newer commit than the installed driver. Both must be pinned to the
driver's revision.
- **The** `include` **list is required, not just an optimisation.** If `flux_specs.rs`  
is checked, Flux crashes with an internal error (`expected enum`, in  
`fhir.rs`). It checks the invariants of the extern-spec'd `ManagedSlice`,  
expects the enum that `managed` defines, and finds the opaque `struct` we  
declared (see 3.2). Restricting `include` to `packet_buffer.rs` and  
`ring_buffer.rs` avoids the crash, and the extern specs still apply.
- **Unclear errors when a flag is ignored.** `FLUXFLAGS=-Finclude=...` did not
override the manifest's `include`. `--only-check` does.

Moving to the extracted crate removed one problem from the smoltcp setup. There,
Flux crashed on `src/socket/dns.rs` even with `include` restricted, because name
resolution runs on the whole crate, so it had to be built without `socket-dns`.
This crate only contains the storage module, so no feature workaround is needed.

### 3.2 Specifying external code

- `managed::ManagedSlice` (the storage type inside `RingBuffer`) needed an extern
spec saying that its `Deref`/`DerefMut` yields a slice of length `len`. Writing
that spec took several attempts:
  - The extern-spec signature has to match the external crate's source *literally*.
  `managed` writes `-> &Self::Target`, so the spec had to be spelled
  `&<ManagedSlice<T> as Deref>::Target[n]`. `&[T][n]` was rejected as structurally
  different.
  - Declaring it as a refined `enum` with variants required `flux-alloc` (for
  `Vec`'s sort), which is not `no_std`. Declaring it as an opaque `struct` avoided
  that, but the file containing it must then be excluded from checking (see 3.1).
- The free function `core::cmp::min` has no spec in `flux-core` (only `Ord::min`
does), so we wrote one.

### 3.3 Flux limitations hit in `PacketBuffer`/`RingBuffer`

- **Internal compiler error on escaping closure borrows.** Every function shaped like
`fn f<'b, F: FnOnce(&'b mut T) -> R>(&'b mut self, f: F)` makes Flux panic
(`incompatible types: †ManagedSlice ...`). This happens with or without our specs.
Affected: `enqueue_one_with`, `dequeue_one_with`, `enqueue_many_with`,
`dequeue_many_with`, and `PacketBuffer::dequeue_with`. These are trusted.
- **Closure bounds can't mention lifetimes.** Flux matches refined `where` clauses
against rustc's clauses exactly, including regions, and its spec syntax cannot
write `'b`. So we could not state "the closure receives a slice of length
`contiguous_window`", which `enqueue_with_infallible` needs. It is trusted.
- **No way to name the return value in** `ensures`**.** "The ring grows by exactly the
number the closure returned" is not expressible for `enqueue_many_with`. So the
four-line wrapper `enqueue_many` is trusted with an exact spec.
- **Losing facts at join points.** `get_unallocated` failed until it got a signature
that fixes `self`'s refinement index (`self: &mut RingBuffer<T>[@b]`). Without
that, each `self.capacity()` call after a mutable borrow of a field sees an
unrelated ring. The arithmetic alone verified fine in isolation.

### 3.4 Properties not proven yet

- `dequeue`**/**`peek` **panic-freedom.** Both call `metadata.header.unwrap()`. This is
only safe because `dequeue_padding()` removes one padding entry and padding entries
are never adjacent. That is a relational invariant across the metadata ring
contents, and our index-only refinements don't track it. Flux correctly reports
the unwraps as unproven, so the two functions are trusted. This is exactly the
"two rings stay consistent" property from the proposal and the natural next target.
- `dequeue_with` **returns** `metadata.size` **bytes.** This needs the same relational
invariant: every metadata entry's `size` matches the bytes it owns in the payload
ring.

## 4 Annotation effort

| File | Lines added | What they are |
|------|-------------|---------------|
| `ring_buffer.rs` | 78 | 29 lines of refinement-level model functions (`defs!`), 6 for the refined struct, about 43 for method specs (one per method on the call paths, most spanning 2–3 lines) |
| `packet_buffer.rs` | 34 | 6 for the refined struct, about 22 for method specs, 6 comment lines explaining the trusted items |
| `flux_specs.rs` (new) | 33 | Extern specs for `ManagedSlice` and `cmp::min` |
| `Cargo.toml`, `mod.rs` | 11 | Flux deps, `cfg(flux)` lint, include list (with a comment on the ICE), `cfg(flux)` module |



Flux is *modular*. It never looks inside a callee and only uses the callee's signature. So proving I3 for `enqueue`
requires precise specs for everything `enqueue` calls: `capacity`, `len`, `window`,
`contiguous_window`, `is_empty`, `is_full`, `clear`, `get_idx`, `enqueue_one`,
`enqueue_many`. Those in turn need the model functions (`rb_idx`, `rb_contig`, ...)
to describe `%` and `min` arithmetic. Also, Flux checks *every* function in an
included file, not only the ones we care about. Each `&mut self` method of
`RingBuffer` must re-establish the struct invariant, and the random-access methods
needed specs just to pass. The invariant itself is two lines. The rest is the cost
of making it checkable everywhere.

## 5 Lessons learned

1. **Runtime asserts silently become assumptions.** Flux does not verify panic paths

   by default, so code after `assert!`/`debug_assert!` assumes the asserted fact.
    Our I3 proof initially passed *because of* the `debug_assert!` in `enqueue`, and
    injected bugs went unnoticed. Always validate specs with injected bugs, and
    remove or `no_panic`-check asserts that duplicate the property being proved. The
    proof does hold without the assert, so the assert can be removed.
2. **Injected-bug testing is essential.** A green run says nothing about spec

   strength. Seven small mutations quickly showed which invariants were really
    enforced.
3. **Index-based refinements are good for "shape" invariants** (lengths,

   capacities, bounds), with high automation once the signatures exist. They are
    poor for *content* invariants (what is stored in the ring), which is where the
    interesting `PacketBuffer` consistency property lives.
4. **Higher-order, borrow-heavy Rust is the main obstacle.** smoltcp's

   closure-passing style (`*_with(|buf| ...)`) is where Flux crashed or could not
    express the spec. That code ended up trusted. This is a useful data point for
    the Flux vs. Verus comparison.
5. **External types need specs before anything works.** One wrapper type

   (`ManagedSlice`) hid all length information until it was specified.
6. **Pin the toolchain.** Flux driver, `flux-rs`, and `flux-core` must be at the

   same revision.
7. **Extract the code under verification.** Flux front-end passes run on the whole

   crate regardless of `include`, so unrelated code can break the run. A minimal  
    crate with only the target modules avoided the `dns.rs` crash and the feature  
    workaround.
