// Injected bugs used to test the Flux specs
//
// This file is for reference only and not compiled.
//
// Bugs 1-3 are only caught when the `debug_assert!` at the end of `enqueue`
// (packet_buffer.rs:126) is also removed.


// ---------------------------------------------------------------------------
// Bug 1: `enqueue` pads one byte too few before wrapping (I3)
// src/storage/packet_buffer.rs, `PacketBuffer::enqueue`, lines 116-126
// ---------------------------------------------------------------------------
                *self.metadata_ring.enqueue_one()? = PacketMetadata::padding(contig_window);
                // note(discard): function does not write to the result
                // enqueued padding buffer location
                let _buf_enqueued = self.payload_ring.enqueue_many(contig_window - 1);
                // CHANGED: was `enqueue_many(contig_window)`
            }
        }

        *self.metadata_ring.enqueue_one()? = PacketMetadata::packet(size, header);

        let payload_buf = self.payload_ring.enqueue_many(size);
        // REMOVED: debug_assert!(payload_buf.len() == size);
        Ok(payload_buf)


// ---------------------------------------------------------------------------
// Bug 2: `enqueue` reserves `size + 1` bytes (I3)
// src/storage/packet_buffer.rs, `PacketBuffer::enqueue`, lines 125-127
// ---------------------------------------------------------------------------
        let payload_buf = self.payload_ring.enqueue_many(size + 1);
        // CHANGED: was `enqueue_many(size)`
        // REMOVED: debug_assert!(payload_buf.len() == size);
        Ok(payload_buf)


// ---------------------------------------------------------------------------
// Bug 3: `enqueue` skips the "padding + packet still fits" check (I3)
// src/storage/packet_buffer.rs, `PacketBuffer::enqueue`, lines 105-126
// ---------------------------------------------------------------------------
        } else if contig_window < size {
            if false {
            // CHANGED: was `if window - contig_window < size {`
                return Err(Full);
            } else {
                // ... (padding is added here, unchanged)
            }
        }

        // ... (unchanged)

        let payload_buf = self.payload_ring.enqueue_many(size);
        // REMOVED: debug_assert!(payload_buf.len() == size);
        Ok(payload_buf)


// ---------------------------------------------------------------------------
// Bug 4: `reset` forgets to clear the payload ring (I2)
// src/storage/packet_buffer.rs, `PacketBuffer::reset`, lines 286-289
// ---------------------------------------------------------------------------
    pub(crate) fn reset(&mut self) {
        // REMOVED: self.payload_ring.clear();
        self.metadata_ring.clear();
    }


// ---------------------------------------------------------------------------
// Bug 5: `enqueue_unallocated` allows `count <= window + 1` (I1)
// src/storage/ring_buffer.rs, `RingBuffer::enqueue_unallocated`, lines 421-424
// ---------------------------------------------------------------------------
    pub fn enqueue_unallocated(&mut self, count: usize) {
        assert!(count <= self.window() + 1);
        // CHANGED: was `assert!(count <= self.window());`
        self.length += count;
    }


// ---------------------------------------------------------------------------
// Bug 6: `get_unallocated` drops the end-of-storage clamp (I1, bounds)
// src/storage/ring_buffer.rs, `RingBuffer::get_unallocated`, lines 380-391
// ---------------------------------------------------------------------------
        // We can't enqueue more than there is free space.
        let clamped_window = self.window() - offset;
        if size > clamped_window {
            size = clamped_window
        }
        // REMOVED:
        // // We can't contiguously enqueue past the end of the storage.
        // let until_end = self.capacity() - start_at;
        // if size > until_end {
        //     size = until_end
        // }

        &mut self.storage[start_at..start_at + size]


// ---------------------------------------------------------------------------
// Bug 7: `dequeue_allocated` forgets to wrap `read_at` (I1)
// src/storage/ring_buffer.rs, `RingBuffer::dequeue_allocated`, lines 475-479
// ---------------------------------------------------------------------------
    pub fn dequeue_allocated(&mut self, count: usize) {
        assert!(count <= self.len());
        self.length -= count;
        self.read_at += count;
        // CHANGED: was `self.read_at = self.get_idx(count);`
    }
