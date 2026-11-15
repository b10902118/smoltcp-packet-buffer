# Extracted Packet Buffer

This independent crate contains the original `PacketBuffer` and `RingBuffer` implementations. It does not depend on smoltcp, compile its networking modules, or run its build script. The Flux-annotated version is in `flux_annotations/`.

### Build

```sh
cargo build
```

### Flux

Install flux globally (recommended because it needs to match your rust version)
https://flux-rs.github.io/flux/guide/install.html

```sh
cd flux_annotations
cargo flux
```

See `flux_annotations/flux_lessons_learned.md` for results and `flux_annotations/injected_bug_tests.md` for injected-bug testing.

### Verus

Download and extract the verus folder to `./.tool/`:
https://github.com/verus-lang/verus/blob/main/INSTALL.md#1-download-the-binary-release

```sh
verus --crate-type=lib [file_to_verify.rs]
```

### Diffs

```diff
--- src/storage/mod.rs
+++ packet-buffer/src/storage/mod.rs
@@ -5,11 +5,9 @@
 or `alloc` crates being available, and heap-allocated memory.
 */

-mod assembler;
 mod packet_buffer;
 mod ring_buffer;

-pub use self::assembler::Assembler;
 pub use self::packet_buffer::{PacketBuffer, PacketMetadata};
 pub use self::ring_buffer::RingBuffer;

```

`mod assembler;` includes the separate assembler implementation, and the removed `pub use` exposes its type to callers. Neither buffer depends on that module. All buffer exports, error types, and the `Resettable` trait remain unchanged.
