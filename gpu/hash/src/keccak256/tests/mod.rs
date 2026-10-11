use era_cudart::memory::{memory_copy_async, DeviceAllocation};
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use worker::Worker;

use super::Digest;
use crate::upstream::Proth120;

mod hash_tests;
mod merkle_tests;

pub(super) const SENTINEL: Digest = [0xaaaa_aaaa; 8];

pub(super) const EDGE_VALUES: [u128; 6] = [
    0,
    1,
    Proth120::ORDER - 1,
    Proth120::ORDER - 2,
    1 << 64,
    1 << 120,
];

pub(super) struct TestRng(u64);

impl TestRng {
    pub(super) fn new(seed: u64) -> Self {
        Self(seed | 1)
    }

    pub(super) fn next_u64(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }

    pub(super) fn field(&mut self) -> Proth120 {
        let value = ((self.next_u64() as u128) << 64) | self.next_u64() as u128;
        Proth120::from_u128_with_reduction(value)
    }
}

pub(super) fn random_columns(rng: &mut TestRng, columns: usize, domain: usize) -> Vec<Proth120> {
    let mut values: Vec<Proth120> = (0..columns * domain).map(|_| rng.field()).collect();
    for (i, value) in EDGE_VALUES.iter().enumerate() {
        values[(i * 37) % domain] = Proth120::new(*value);
        values[domain - 1 - (i * 11) % domain] = Proth120::new(*value);
    }
    values
}

pub(super) fn upload<T: Copy>(host: &[T], stream: &CudaStream) -> DeviceAllocation<T> {
    let mut device = DeviceAllocation::alloc(host.len()).unwrap();
    memory_copy_async(&mut device, host, stream).unwrap();
    device
}

pub(super) fn download<T: Copy>(device: &DeviceSlice<T>, fill: T, stream: &CudaStream) -> Vec<T> {
    let mut host = vec![fill; device.len()];
    memory_copy_async(&mut host, device, stream).unwrap();
    stream.synchronize().unwrap();
    host
}

pub(super) fn bitreverse_index(index: usize, bits: u32) -> usize {
    if bits == 0 {
        0
    } else {
        index.reverse_bits() >> (usize::BITS - bits)
    }
}

pub(super) fn test_worker() -> Worker {
    Worker::new_with_num_threads(4)
}
