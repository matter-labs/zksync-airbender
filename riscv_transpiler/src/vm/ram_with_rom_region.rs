use crate::vm::{RamPeek, Register, RAM};
use common_constants::*;
use field::PrimeField;
use std::alloc::{self, Allocator, Layout};

/// Allocate a zeroed `Vec<Register>` without touching every backing page.
///
/// `RamWithRomRegion` can reserve a full 1 GiB VM address space. A `vec![...; N]`
/// initialization writes every register eagerly, which forces the OS to commit
/// the entire virtual allocation. `alloc_zeroed` lets the allocator/kernel serve
/// zero pages lazily, so only pages actually written during execution consume
/// physical memory.
///
/// # Safety
///
/// `Register` is a `Copy` plain-data value and the all-zero byte pattern is a
/// valid representation of `Register { timestamp: 0, value: 0 }`.
fn alloc_zeroed_registers(count: usize) -> Vec<Register> {
    if count == 0 {
        return Vec::new();
    }

    unsafe {
        let layout =
            Layout::array::<Register>(count).expect("register allocation layout should fit");
        let ptr = alloc::alloc_zeroed(layout) as *mut Register;
        if ptr.is_null() {
            alloc::handle_alloc_error(layout);
        }

        Vec::from_raw_parts(ptr, count, count)
    }
}

pub struct RamWithRomRegion<const ROM_BOUND_SECOND_WORD_BITS: usize> {
    pub(crate) backing: Vec<Register>,
}

impl<const ROM_BOUND_SECOND_WORD_BITS: usize> RamWithRomRegion<ROM_BOUND_SECOND_WORD_BITS> {
    pub fn from_rom_content(content: &[u32], total_size_bytes: usize) -> Self {
        assert!(
            total_size_bytes.is_power_of_two(),
            "total size {} is not power of two",
            total_size_bytes
        );
        let rom_bytes = 1 << (16 + ROM_BOUND_SECOND_WORD_BITS);
        assert!(total_size_bytes > rom_bytes);
        let num_rom_words = rom_bytes / core::mem::size_of::<u32>();

        assert!(content.len() <= num_rom_words);
        let ram_words = total_size_bytes / core::mem::size_of::<u32>();

        let mut backing = alloc_zeroed_registers(ram_words);
        for (dst, src) in backing.iter_mut().zip(content.iter()) {
            dst.value = *src;
        }

        Self { backing }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vm::RAM;

    #[test]
    fn alloc_zeroed_registers_are_valid() {
        let registers = alloc_zeroed_registers(64);

        for register in registers.iter() {
            assert_eq!(register.value, 0);
            assert_eq!(register.timestamp, 0);
        }
    }

    #[test]
    fn alloc_zeroed_registers_empty() {
        let registers = alloc_zeroed_registers(0);

        assert!(registers.is_empty());
    }

    #[test]
    fn from_rom_content_preserves_read_write_behavior() {
        let total_size = 1 << 17;
        let rom_words = (1 << 16) / core::mem::size_of::<u32>();
        let content: Vec<u32> = (0..rom_words as u32).collect();

        let mut ram = RamWithRomRegion::<0>::from_rom_content(&content, total_size);

        for i in 0..rom_words {
            assert_eq!(ram.peek_word(i as u32 * 4), i as u32);
        }

        let ram_addr = rom_words as u32 * 4;
        assert_eq!(ram.peek_word(ram_addr), 0);

        let (old_timestamp, old_value) = ram.write_word(ram_addr, 0xDEAD_BEEF, 4);
        assert_eq!(old_timestamp, 0);
        assert_eq!(old_value, 0);

        let (read_timestamp, read_value) = ram.read_word(ram_addr, 8);
        assert_eq!(read_timestamp, 4 | 2);
        assert_eq!(read_value, 0xDEAD_BEEF);
    }
}

pub const fn timestamp_scalar_into_column_values(
    timestamp: TimestampScalar,
) -> [u32; NUM_TIMESTAMP_COLUMNS_FOR_RAM] {
    let low = timestamp & ((1 << TIMESTAMP_COLUMNS_NUM_BITS) - 1);
    let high = timestamp >> TIMESTAMP_COLUMNS_NUM_BITS;

    [low as u32, high as u32]
}

pub fn split_u32_into_pair_u16(num: u32) -> (u16, u16) {
    let high_word = (num >> 16) as u16;
    let low_word = (num & 0xffff) as u16;
    (low_word, high_word)
}

pub fn split_timestamp(timestamp: TimestampScalar) -> (u32, u32) {
    let [low, high] = timestamp_scalar_into_column_values(timestamp);

    (low, high)
}

// NOTE: we will not branch and special-case here to model ROM reads as reads from address 0 of 0 value,
// and witness post-processing can track it. Instead we will only track last access for snapshotting purposes

impl<const ROM_BOUND_SECOND_WORD_BITS: usize> RamPeek
    for RamWithRomRegion<ROM_BOUND_SECOND_WORD_BITS>
{
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
}

impl<const ROM_BOUND_SECOND_WORD_BITS: usize> RAM for RamWithRomRegion<ROM_BOUND_SECOND_WORD_BITS> {
    #[inline(always)]
    fn mask_read_for_witness(&self, _address: &mut u32, _value: &mut u32) {
        // we do not do anything here
    }

    #[inline(always)]
    fn read_word(&mut self, address: u32, timestamp: TimestampScalar) -> (TimestampScalar, u32) {
        // NOTE: for simplicity of the JIT based simulator we will avoid masking address into 0 here for ROM access,
        // and instead will give a timestamp of requested address. In replayer we will mask a value
        debug_assert_eq!(address % 4, 0);
        unsafe {
            let word_idx = (address / 4) as usize;
            debug_assert!(word_idx < self.backing.len());
            let slot = self.backing.get_unchecked_mut(word_idx);
            let value = slot.value;
            let read_timestamp = slot.timestamp;
            slot.timestamp = timestamp | 1;

            debug_assert!(read_timestamp < timestamp | 1);

            // println!("Read at address 0x{:08x} at timestamp {} into value {} and read timestamp {}", address, timestamp, value, read_timestamp);

            // NOTE: value here will allow us to replay based on log only,
            // but timestamp will allow us to use it later on for witness gen

            (read_timestamp, value)
        }
    }

    #[inline(always)]
    fn skip_if_replaying(&mut self, _num_snapshots: usize) {
        panic!("mustn not be used in replayer");
    }

    // #[inline(always)]
    // fn read_word(&mut self, address: u32, timestamp: TimestampScalar) -> (TimestampScalar, u32) {
    //     debug_assert_eq!(address % 4, 0);
    //     unsafe {
    //         let word_idx = (address / 4) as usize;
    //         debug_assert!(word_idx < self.backing.len());
    //         let value;
    //         let read_timestamp;
    //         if word_idx < (1 << (16 + ROM_BOUND_SECOND_WORD_BITS)) / core::mem::size_of::<u32>() {
    //             // value is from real slot, but we mask the access
    //             value = self.backing.get_unchecked(word_idx).value;
    //             // Track access as reading 0 slot
    //             let zero_slot = self.backing.get_unchecked_mut(0);
    //             read_timestamp = zero_slot.timestamp;
    //             zero_slot.timestamp = timestamp | 1;
    //         } else {
    //             let slot = self.backing.get_unchecked_mut(word_idx);
    //             value = slot.value;
    //             read_timestamp = slot.timestamp;
    //             slot.timestamp = timestamp | 1;
    //         }

    //         debug_assert!(read_timestamp < timestamp | 1);

    //         // println!("Read at address 0x{:08x} at timestamp {} into value {} and read timestamp {}", address, timestamp, value, read_timestamp);

    //         // NOTE: value here will allow us to replay based on log only,
    //         // but timestamp will allow us to use it later on for witness gen
    //         // when such reads would be masked into reading from 0 address

    //         (read_timestamp, value)
    //     }
    // }

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
                panic!("attempt to write into ROM range");
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
                        if word.timestamp != 0 {
                            let mut word_value = word.value;
                            // we mask ROM region to be zero-valued
                            if address < (1 << (16 + ROM_BOUND_SECOND_WORD_BITS)) {
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

    pub fn collect_inits_and_teardowns_into_columns<
        F: PrimeField,
        A: Allocator + Clone + Send + Sync,
    >(
        &self,
        worker: &worker::Worker,
        words_per_chunk_log2: usize,
        offset_in_words: usize,
        column_chunks: &mut [([Vec<F, A>; 2], [Vec<F, A>; 2])], // ts, value
    ) {
        use common_constants::*;

        // parallel collect, and we access mutually exclusive places, so we first degrate everything to pointers
        // first we will walk over access_bitmask and collect subparts

        let words_per_chunk = 1 << words_per_chunk_log2;
        assert_eq!(offset_in_words % words_per_chunk, 0);
        let dst_size_words = words_per_chunk * column_chunks.len();
        for el in column_chunks.iter() {
            let ([a, b], [c, d]) = el;
            assert_eq!(a.len(), 0);
            assert_eq!(b.len(), 0);
            assert_eq!(c.len(), 0);
            assert_eq!(d.len(), 0);
        }

        // we do not support overfills yet
        assert!(offset_in_words + dst_size_words <= self.backing.len());

        worker.scope(dst_size_words, |scope, geometry| {
            for thread_idx in 0..geometry.len() {
                let t = unsafe {
                    let ptr = column_chunks.as_mut_ptr();
                    let len = column_chunks.len();

                    core::slice::from_raw_parts_mut(ptr, len)
                };
                let mut mapped = Vec::with_capacity(t.len());
                for ([a, b], [c, d]) in t.iter_mut() {
                    mapped.push((
                        [
                            &mut a.spare_capacity_mut()[..words_per_chunk],
                            &mut b.spare_capacity_mut()[..words_per_chunk],
                        ],
                        [
                            &mut c.spare_capacity_mut()[..words_per_chunk],
                            &mut d.spare_capacity_mut()[..words_per_chunk],
                        ],
                    ));
                }
                let chunk_size = geometry.get_chunk_size(thread_idx);
                let chunk_start = geometry.get_chunk_start_pos(thread_idx);
                let start = offset_in_words + chunk_start;
                let end = start + chunk_size;
                let src = &self.backing[start..end];

                worker::Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                    let mut word_idx = start;
                    for word in src.iter() {
                        let in_chunk_idx = word_idx % (1 << words_per_chunk_log2);
                        let chunk_idx = (word_idx - offset_in_words) >> words_per_chunk_log2;
                        let address = word_idx * core::mem::size_of::<u32>();

                        let mut word_value = word.value;
                        // we mask ROM region to be zero-valued
                        if address < (1 << (16 + ROM_BOUND_SECOND_WORD_BITS)) {
                            word_value = 0;
                        }
                        let last_timestamp: TimestampScalar = word.timestamp;
                        let (val_low, val_high) = split_u32_into_pair_u16(word_value);
                        let (ts_low, ts_high) = split_timestamp(last_timestamp);

                        mapped[chunk_idx].0[0][in_chunk_idx]
                            .write(F::from_u32_unchecked(ts_low as u32));
                        mapped[chunk_idx].0[1][in_chunk_idx]
                            .write(F::from_u32_unchecked(ts_high as u32));

                        mapped[chunk_idx].1[0][in_chunk_idx]
                            .write(F::from_u32_unchecked(val_low as u32));
                        mapped[chunk_idx].1[1][in_chunk_idx]
                            .write(F::from_u32_unchecked(val_high as u32));

                        word_idx += 1;
                    }
                });
            }
        });

        unsafe {
            for ([a, b], [c, d]) in column_chunks.iter_mut() {
                a.set_len(words_per_chunk);
                b.set_len(words_per_chunk);
                c.set_len(words_per_chunk);
                d.set_len(words_per_chunk);
            }
        }
    }

    pub fn collect_inits_and_teardowns_sets<
        F: PrimeField,
        A: Allocator + Clone + Send + Sync + Default,
    >(
        &self,
        worker: &worker::Worker,
        words_per_chunk_log2: usize,
        chunks_in_set: usize,
        upper_ram_bound_hint_in_words: Option<usize>,
    ) -> Vec<(Vec<u32>, Vec<([Vec<F, A>; 2], [Vec<F, A>; 2])>)> // ts, value
    {
        assert!(chunks_in_set > 0);
        assert!(
            chunks_in_set <= 2,
            "we do not support logic for generic grouping of chunks yet"
        );
        // parallel collect, and we access mutually exclusive places, so we first degrate everything to pointers
        // first we will walk over access_bitmask and collect subparts

        let (sender, receiver) = std::sync::mpsc::channel();

        let words_upper_bound = std::cmp::min(
            upper_ram_bound_hint_in_words.unwrap_or(usize::MAX),
            self.backing.len(),
        );
        let num_chunks = words_upper_bound.div_ceil(1 << words_per_chunk_log2);

        worker.scope(num_chunks, |scope, geometry| {
            for thread_idx in 0..geometry.len() {
                let sender = sender.clone();
                let chunk_size = geometry.get_chunk_size(thread_idx);
                let chunk_start = geometry.get_chunk_start_pos(thread_idx);

                worker::Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                    let mut buffer = (
                        [
                            Vec::with_capacity_in(1 << words_per_chunk_log2, A::default()),
                            Vec::with_capacity_in(1 << words_per_chunk_log2, A::default()),
                        ],
                        [
                            Vec::with_capacity_in(1 << words_per_chunk_log2, A::default()),
                            Vec::with_capacity_in(1 << words_per_chunk_log2, A::default()),
                        ],
                    );
                    buffer.0[0].resize(1 << words_per_chunk_log2, F::ZERO);
                    buffer.0[1].resize(1 << words_per_chunk_log2, F::ZERO);
                    buffer.1[0].resize(1 << words_per_chunk_log2, F::ZERO);
                    buffer.1[1].resize(1 << words_per_chunk_log2, F::ZERO);

                    for chunk_idx in chunk_start..chunk_start + chunk_size {
                        let start = chunk_idx * (1 << words_per_chunk_log2);
                        let src = &self.backing[start..][..1 << words_per_chunk_log2];
                        let mut non_trivial_word = false;
                        let top_bits = chunk_idx as u32;
                        let mut word_idx = start;
                        for (buffer_idx, word) in src.iter().enumerate() {
                            let address = word_idx * core::mem::size_of::<u32>();
                            let mut word_value = word.value;
                            // we mask ROM region to be zero-valued
                            if address < (1 << (16 + ROM_BOUND_SECOND_WORD_BITS)) {
                                word_value = 0;
                            }
                            let last_timestamp: TimestampScalar = word.timestamp;
                            if last_timestamp != 0 {
                                non_trivial_word = true;
                            }
                            let (val_low, val_high) = split_u32_into_pair_u16(word_value);
                            let (ts_low, ts_high) = split_timestamp(last_timestamp);

                            buffer.0[0][buffer_idx] = F::from_u32_unchecked(ts_low as u32);
                            buffer.0[1][buffer_idx] = F::from_u32_unchecked(ts_high as u32);

                            buffer.1[0][buffer_idx] = F::from_u32_unchecked(val_low as u32);
                            buffer.1[1][buffer_idx] = F::from_u32_unchecked(val_high as u32);

                            word_idx += 1;
                        }

                        if non_trivial_word {
                            // send and replace buffer
                            let mut t = (
                                [
                                    Vec::with_capacity_in(1 << words_per_chunk_log2, A::default()),
                                    Vec::with_capacity_in(1 << words_per_chunk_log2, A::default()),
                                ],
                                [
                                    Vec::with_capacity_in(1 << words_per_chunk_log2, A::default()),
                                    Vec::with_capacity_in(1 << words_per_chunk_log2, A::default()),
                                ],
                            );
                            t.0[0].resize(1 << words_per_chunk_log2, F::ZERO);
                            t.0[1].resize(1 << words_per_chunk_log2, F::ZERO);
                            t.1[0].resize(1 << words_per_chunk_log2, F::ZERO);
                            t.1[1].resize(1 << words_per_chunk_log2, F::ZERO);

                            let buffer_to_send = std::mem::replace(&mut buffer, t);
                            sender
                                .send((top_bits, buffer_to_send))
                                .expect("must send to unbounded channel");
                        }
                    }
                });
            }
        });

        let mut result = vec![];
        while let Ok((top_bits, buffer)) = receiver.try_recv() {
            result.push((top_bits, buffer));
        }

        result.sort_by(|a, b| a.0.cmp(&b.0));

        let num_extra_elements = result.len() % chunks_in_set;
        let need_extra_element = num_extra_elements != 0;
        let groups = result.len().div_ceil(chunks_in_set);

        let mut grouped = vec![];
        if need_extra_element == false {
            let mut it = result.into_iter();
            for _ in 0..groups {
                let mut chunk = (vec![], vec![]);
                for _ in 0..chunks_in_set {
                    let (bits, inits) = it.next().unwrap();
                    chunk.0.push(bits);
                    chunk.1.push(inits);
                }
                grouped.push(chunk);
            }
        } else {
            assert_eq!(num_extra_elements, 1);
            let min_top_bits = result.iter().map(|el| el.0).min().unwrap();
            // let max_top_bits = result.iter().map(|el| el.0).max().unwrap();
            let top_bits_beyond_bound = self.backing.len().div_ceil(1 << words_per_chunk_log2);
            let padding_bits_to_use = if min_top_bits > 0 {
                0u32
            } else {
                top_bits_beyond_bound as u32
            };
            let bound = result.len();
            let mut chunk = (vec![], vec![]);
            if padding_bits_to_use == 0 {
                let mut t = (
                    [
                        Vec::with_capacity_in(1 << words_per_chunk_log2, A::default()),
                        Vec::with_capacity_in(1 << words_per_chunk_log2, A::default()),
                    ],
                    [
                        Vec::with_capacity_in(1 << words_per_chunk_log2, A::default()),
                        Vec::with_capacity_in(1 << words_per_chunk_log2, A::default()),
                    ],
                );
                t.0[0].resize(1 << words_per_chunk_log2, F::ZERO);
                t.0[1].resize(1 << words_per_chunk_log2, F::ZERO);
                t.1[0].resize(1 << words_per_chunk_log2, F::ZERO);
                t.1[1].resize(1 << words_per_chunk_log2, F::ZERO);

                chunk.0.push(padding_bits_to_use);
                chunk.1.push(t);
            }
            let mut it = result.into_iter();
            for _ in 0..bound {
                let (bits, inits) = it.next().unwrap();
                chunk.0.push(bits);
                chunk.1.push(inits);
                if chunk.0.len() == chunks_in_set {
                    let t = std::mem::take(&mut chunk);
                    grouped.push(t);
                }
            }
            assert!(it.next().is_none());
            if padding_bits_to_use == (top_bits_beyond_bound as u32) {
                let mut t = (
                    [
                        Vec::with_capacity_in(1 << words_per_chunk_log2, A::default()),
                        Vec::with_capacity_in(1 << words_per_chunk_log2, A::default()),
                    ],
                    [
                        Vec::with_capacity_in(1 << words_per_chunk_log2, A::default()),
                        Vec::with_capacity_in(1 << words_per_chunk_log2, A::default()),
                    ],
                );
                t.0[0].resize(1 << words_per_chunk_log2, F::ZERO);
                t.0[1].resize(1 << words_per_chunk_log2, F::ZERO);
                t.1[0].resize(1 << words_per_chunk_log2, F::ZERO);
                t.1[1].resize(1 << words_per_chunk_log2, F::ZERO);

                chunk.0.push(padding_bits_to_use);
                chunk.1.push(t);

                assert_eq!(chunk.0.len(), chunks_in_set);
                grouped.push(chunk);
            }
        }

        grouped
    }
}
