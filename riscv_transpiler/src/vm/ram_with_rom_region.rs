use std::alloc::Allocator;

use common_constants::TimestampScalar;

use crate::vm::{Register, RAM};

pub struct RamWithRomRegion<const ROM_BOUND_SECOND_WORD_BITS: usize> {
    backing: Vec<Register>,
}

impl<const ROM_BOUND_SECOND_WORD_BITS: usize> RamWithRomRegion<ROM_BOUND_SECOND_WORD_BITS> {
    pub fn from_rom_content(content: &[u32], total_size_bytes: usize) -> Self {
        assert!(total_size_bytes.is_power_of_two());
        let rom_bytes = 1 << (16 + ROM_BOUND_SECOND_WORD_BITS);
        assert!(total_size_bytes > rom_bytes);
        let num_rom_words = rom_bytes / core::mem::size_of::<u32>();

        assert!(content.len() <= num_rom_words);
        let ram_words = total_size_bytes / core::mem::size_of::<u32>();

        let mut backing = vec![
            Register {
                value: 0,
                timestamp: 0
            };
            ram_words
        ];
        for (dst, src) in backing.iter_mut().zip(content.iter()) {
            dst.value = *src;
        }

        Self { backing }
    }
}

// NOTE: we will not branch and special-case here to model ROM reads as reads from address 0 of 0 value,
// and witness post-processing can track it. Instead we will only track last access for snapshotting purposes

impl<const ROM_BOUND_SECOND_WORD_BITS: usize> RAM for RamWithRomRegion<ROM_BOUND_SECOND_WORD_BITS> {
    #[inline(always)]
    fn peek_word(&self, address: u32) -> u32 {
        debug_assert_eq!(address % 4, 0);
        unsafe {
            let word_idx = (address / 4) as usize;
            debug_assert!(word_idx < self.backing.len());
            let slot = self.backing.get_unchecked(word_idx);
            let value = slot.value;

            value
        }
    }

    #[inline(always)]
    fn mask_read_for_witness(&self, _address: &mut u32, _value: &mut u32) {
        // we do not do anything here
    }

    #[inline(always)]
    fn read_word(&mut self, address: u32, timestamp: TimestampScalar) -> (TimestampScalar, u32) {
        debug_assert_eq!(address % 4, 0);
        unsafe {
            let word_idx = (address / 4) as usize;
            debug_assert!(word_idx < self.backing.len());
            let value;
            let read_timestamp;
            if word_idx < (1 << (16 + ROM_BOUND_SECOND_WORD_BITS)) / core::mem::size_of::<u32>() {
                // value is from real slot, but we mask the access
                value = self.backing.get_unchecked(word_idx).value;
                // Track access as reading 0 slot
                let zero_slot = self.backing.get_unchecked_mut(0);
                read_timestamp = zero_slot.timestamp;
                zero_slot.timestamp = timestamp | 1;
            } else {
                let slot = self.backing.get_unchecked_mut(word_idx);
                value = slot.value;
                read_timestamp = slot.timestamp;
                slot.timestamp = timestamp | 1;
            }

            debug_assert!(read_timestamp < timestamp | 1);

            // println!("Read at address 0x{:08x} at timestamp {} into value {} and read timestamp {}", address, timestamp, value, read_timestamp);

            // NOTE: value here will allow us to replay based on log only,
            // but timestamp will allow us to use it later on for witness gen
            // when such reads would be masked into reading from 0 address

            (read_timestamp, value)
        }
    }

    #[inline(always)]
    fn write_word(
        &mut self,
        address: u32,
        word: u32,
        timestamp: TimestampScalar,
    ) -> (TimestampScalar, u32) {
        debug_assert_eq!(address % 4, 0);
        unsafe {
            let word_idx = (address / 4) as usize;
            debug_assert!(word_idx < self.backing.len());
            if word_idx < (1 << (16 + ROM_BOUND_SECOND_WORD_BITS)) / core::mem::size_of::<u32>() {
                panic!();
            }
            let slot = self.backing.get_unchecked_mut(word_idx);
            let old_value = slot.value;
            let read_timestamp = slot.timestamp;
            debug_assert!(read_timestamp < timestamp | 2);
            slot.value = word;
            slot.timestamp = timestamp | 2;

            // println!("Write at address 0x{:08x} at timestamp {} of value {} into value {} and read timestamp {}", address, timestamp, word, old_value, read_timestamp);

            (read_timestamp, old_value)
        }
    }
}

impl<const ROM_BOUND_SECOND_WORD_BITS: usize> RamWithRomRegion<ROM_BOUND_SECOND_WORD_BITS> {
    pub fn collect_inits_and_teardowns<A: Allocator + Clone + Send + Sync>(
        &self,
        worker: &worker::Worker,
        allocator: A,
    ) -> Vec<Vec<(u32, (TimestampScalar, u32)), A>> {
        // parallel collect
        // first we will walk over access_bitmask and collect subparts
        let mut chunks: Vec<Vec<(u32, (TimestampScalar, u32)), A>> =
            vec![Vec::new_in(allocator).clone(); worker.get_num_cores()];
        let mut dst = &mut chunks[..];
        worker.scope(self.backing.len(), |scope, geometry| {
            for thread_idx in 0..geometry.len() {
                let chunk_size = geometry.get_chunk_size(thread_idx);
                let chunk_start = geometry.get_chunk_start_pos(thread_idx);
                let range = chunk_start..(chunk_start + chunk_size);
                let (el, rest) = dst.split_at_mut(1);
                dst = rest;
                let src = &self.backing[range];

                worker::Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                    let el = &mut el[0];
                    let mut address = chunk_start * core::mem::size_of::<u32>();
                    for word in src.iter() {
                        if address < (1 + (16 + ROM_BOUND_SECOND_WORD_BITS)) {
                            if address != 0 {
                                assert_eq!(
                                    word.timestamp, 0,
                                    "non-zero access timestamp in ROM region at address 0x{:08x}",
                                    address
                                );
                            }
                        }

                        if word.timestamp != 0 {
                            let mut word_value = word.value;
                            // we mask ROM region to be zero-valued
                            if address < (1 + (16 + ROM_BOUND_SECOND_WORD_BITS)) {
                                word_value = 0;
                            }
                            let last_timestamp: TimestampScalar = word.timestamp;
                            el.push((address as u32, (last_timestamp, word_value)));
                        }

                        address += core::mem::size_of::<u32>();
                    }
                });
            }
        });

        chunks
    }
}
