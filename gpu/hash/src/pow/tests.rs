use era_cudart::memory::{memory_copy_async, DeviceAllocation};
use era_cudart::result::CudaResult;
use era_cudart::slice::{DeviceSlice, DeviceVariable};
use era_cudart::stream::CudaStream;
use sha3::{Digest as _, Keccak256};

use crate::upstream::{Blake2sState, USE_REDUCED_BLAKE2_ROUNDS};

trait Hash {
    const MAX_BITS: u32;

    fn matches(seed: &[u8; 32], nonce: u64, bits: u32) -> bool;

    fn search(
        seed: &DeviceSlice<u8>,
        bits: u32,
        blocks: u32,
        first_chunk: u64,
        result: &mut DeviceVariable<u64>,
        counter: &mut DeviceVariable<u64>,
        stream: &CudaStream,
    ) -> CudaResult<()>;
}

struct Blake2s;
struct Keccak;

impl Hash for Blake2s {
    const MAX_BITS: u32 = 32;

    fn matches(seed: &[u8; 32], nonce: u64, bits: u32) -> bool {
        let mut block = [0; 16];
        for (slot, bytes) in block[..8].iter_mut().zip(seed.as_chunks::<4>().0) {
            *slot = u32::from_le_bytes(*bytes);
        }
        block[8] = nonce as u32;
        block[9] = (nonce >> 32) as u32;
        let mut digest = [0; 8];
        Blake2sState::new().absorb_final_block::<USE_REDUCED_BLAKE2_ROUNDS>(
            &block,
            10,
            &mut digest,
        );
        digest[0].leading_zeros() >= bits
    }

    fn search(
        seed: &DeviceSlice<u8>,
        bits: u32,
        blocks: u32,
        first_chunk: u64,
        result: &mut DeviceVariable<u64>,
        counter: &mut DeviceVariable<u64>,
        stream: &CudaStream,
    ) -> CudaResult<()> {
        crate::blake2s::blake2s_pow_search_bounded(
            // SAFETY: test seeds use a whole CUDA allocation with 32 bytes and u32 alignment.
            unsafe { seed.transmute::<u32>() },
            bits,
            u64::MAX,
            blocks,
            first_chunk,
            result,
            counter,
            stream,
        )
    }
}

impl Hash for Keccak {
    const MAX_BITS: u32 = 256;

    fn matches(seed: &[u8; 32], nonce: u64, bits: u32) -> bool {
        let mut hash = Keccak256::new();
        hash.update(seed);
        hash.update(nonce.to_be_bytes());
        let digest = hash.finalize();
        let bytes = (bits / 8) as usize;
        let partial = bits % 8;
        digest[..bytes].iter().all(|byte| *byte == 0)
            && (partial == 0 || digest[bytes] >> (8 - partial) == 0)
    }

    fn search(
        seed: &DeviceSlice<u8>,
        bits: u32,
        blocks: u32,
        first_chunk: u64,
        result: &mut DeviceVariable<u64>,
        counter: &mut DeviceVariable<u64>,
        stream: &CudaStream,
    ) -> CudaResult<()> {
        crate::keccak256::pow_search_bounded(
            seed,
            bits,
            u64::MAX,
            blocks,
            first_chunk,
            result,
            counter,
            stream,
        )
    }
}

fn check_nonce_top<H: Hash>() {
    let stream = CudaStream::default();
    let seed = [0x3c; 32];
    let mut device_seed = DeviceAllocation::alloc(seed.len()).unwrap();
    memory_copy_async(&mut device_seed, &seed, &stream).unwrap();
    let mut result = DeviceAllocation::alloc(1).unwrap();
    let mut counter = DeviceAllocation::alloc(1).unwrap();
    let mut run = |bits, blocks, first_chunk| {
        H::search(
            &device_seed,
            bits,
            blocks,
            first_chunk,
            &mut result[0],
            &mut counter[0],
            &stream,
        )
        .unwrap();
        let mut host = [0; 2];
        memory_copy_async(&mut host[..1], &result, &stream).unwrap();
        memory_copy_async(&mut host[1..], &counter, &stream).unwrap();
        stream.synchronize().unwrap();
        (host[0], host[1])
    };
    let first_chunk = u64::MAX / 32 - 4;
    let first_hit = (first_chunk * 32..u64::MAX)
        .find(|&nonce| H::matches(&seed, nonce, 4))
        .unwrap();
    for blocks in [1, 2, 17] {
        assert_eq!(super::pow_chunk_steps(4, blocks), 1);
        assert_eq!(run(4, blocks, first_chunk).0, first_hit);
    }
    let chunk = 32 * u64::from(super::pow_chunk_steps(H::MAX_BITS, 1));
    let last_chunk = (u64::MAX - 1) / chunk;
    assert!((last_chunk * chunk..u64::MAX).all(|nonce| !H::matches(&seed, nonce, H::MAX_BITS)));
    assert_eq!(run(H::MAX_BITS, 1, last_chunk), (u64::MAX, last_chunk + 5));
    assert_eq!(
        run(H::MAX_BITS, 1, u64::MAX / 32),
        (u64::MAX, u64::MAX / 32 + 4),
    );
}

#[test]
fn pow_counter_reaches_top_of_nonce_domain() {
    check_nonce_top::<Blake2s>();
    check_nonce_top::<Keccak>();
}
