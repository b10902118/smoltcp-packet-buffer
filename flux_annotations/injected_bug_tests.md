# Injected-Bug Testing of the Flux Specs

A passing `cargo flux` run only shows that the code satisfies the specs. It does not
show that the specs are strong enough to rule out real mistakes. To check that, we
injected seven small bugs into `RingBuffer` and `PacketBuffer` and confirmed that
Flux rejects each one. The exact edits are in `injected_bugs.rs`.

## Method

- Each test starts from the verified crate, which passes `cargo flux` (39 functions
  checked, 15 trusted, 54 constraints solved).
- Exactly one bug is introduced per test, by changing a single line or block. Specs
  and annotations are never changed. The edit is reverted before the next test.
- A bug counts as **caught** if Flux reports a refinement type error
  (`error[E0999]`). A Rust compile error or a Flux crash would not count.
- Bugs 1–3 were run twice: with and without the
  `debug_assert!(payload_buf.len() == size)` at the end of `enqueue`.

The bugs were first run in the full smoltcp crate and then repeated in this crate
with the same results.

Invariants: **I1** every ring is well-formed (`len <= cap`, `read_at < cap` or
`read_at == 0` when `cap == 0`) and every slice index is in bounds. **I2**
`PacketBuffer` capacities never change and `reset()` empties both rings. **I3** on
success, `enqueue(size)` returns exactly `size` bytes.

## Results

| # | Injected bug | Invariant | Result | Where Flux reports it |
|---|--------------|-----------|--------|-----------------------|
| 1 | `enqueue` pads one byte too few before wrapping | I3 | caught* | `Ok(payload_buf)` in `enqueue` |
| 2 | `enqueue` reserves `size + 1` bytes | I3 | caught* | `Ok(payload_buf)` in `enqueue` |
| 3 | `enqueue` skips the "padding + packet still fits" check | I3 | caught* | `Ok(payload_buf)` in `enqueue` |
| 4 | `reset` forgets to clear the payload ring | I2 | caught | body of `reset` |
| 5 | `enqueue_unallocated` allows `count <= window + 1` | I1 | caught | end of `enqueue_unallocated` |
| 6 | `get_unallocated` drops the end-of-storage clamp | I1 (bounds) | caught | slice `storage[start_at..start_at + size]` |
| 7 | `dequeue_allocated` forgets to wrap `read_at` | I1 | caught | end of `dequeue_allocated` |

\* Caught only with the `debug_assert!` removed. With it present, Flux misses
all three.

## Why each bug is caught

1. **Padding one byte short.** The write position stops one byte before the end of
   the storage, so the next `enqueue_many(size)` can only return one byte. The spec
   of `enqueue_many` gives a length of `min(size, contiguous window)`, and Flux
   cannot show this equals `size`, which the return type `&mut [u8][size]` requires.
2. **Reserving `size + 1`.** The returned slice has length
   `min(size + 1, contiguous window)`, which is not always `size`.
3. **Skipping the fit check.** After padding, the contiguous space at the start of
   the ring is `window - contig_window`. Without the check, Flux cannot show that
   this is at least `size`.
4. **`reset` keeping the payload.** The spec of `reset` promises `plen == 0`, but the
   payload ring is left untouched.
5. **Off-by-one in `enqueue_unallocated`.** The loosened assertion only gives
   `len <= cap + 1`, so the struct invariant `len <= cap` cannot be re-established
   when the function returns.
6. **No end-of-storage clamp.** The range-indexing spec from `flux-core` requires
   `start_at + size <= len`, which no longer holds when free space wraps around.
7. **Unwrapped `read_at`.** `read_at + count` can reach or exceed `cap`, breaking the
   struct invariant `read_at < cap` when the function returns.

Bugs 5 and 7 are in functions with no spec of their own. They are caught only
because every `&mut self` method must restore the `RingBuffer` struct invariant.

## Role of the `debug_assert!`

With `debug_assert!(payload_buf.len() == size)` still in `enqueue`, Flux accepted
bugs 1–3. Flux does not check that assertions hold. It treats the code after an
`assert!` or `debug_assert!` as running only when the condition is true, so the
assertion supplied exactly the fact the return type needed. The bug moved from a type
error to a debug-build panic, which Flux does not report by default.

After the line was removed, all three were caught, and the unmodified crate still
verifies, so I3 really does hold. The assertion is kept in the source so the crate
stays identical to smoltcp apart from annotations. Removing it, or checking it with
`#[no_panic]`, is a next step.

## Takeaways

- All seven bugs are caught, so the specs constrain behaviour and are not just
  satisfied trivially.
- Struct invariants do much of the work, even in functions with no spec.
- Runtime assertions can hide bugs from Flux. Any assertion that restates the property
  being proved should be removed or checked with `#[no_panic]` before the proof is
  trusted.
