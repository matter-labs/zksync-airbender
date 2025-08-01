use super::callbacks::Callbacks;
use super::context::{HostAllocation, ProverContext};
use crate::allocator::tracker::AllocationPlacement;
use crate::blake2s::{blake2s_pow, STATE_SIZE};
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use prover::transcript::{Blake2sTranscript, Seed};
use std::slice;

pub(crate) struct PowOutput {
    pub nonce: HostAllocation<u64>,
}

impl PowOutput {
    pub fn new<'a>(
        seed: &mut HostAllocation<Seed>,
        pow_bits: u32,
        external_nonce: Option<u64>,
        callbacks: &mut Callbacks<'a>,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        let seed_accessor = seed.get_mut_accessor();
        let mut nonce = unsafe { context.alloc_host_uninit::<u64>() };
        let nonce_accessor = nonce.get_mut_accessor();
        let stream = context.get_exec_stream();
        if let Some(external_nonce) = external_nonce {
            let set_nonce_fn = move || unsafe {
                nonce_accessor.set(external_nonce);
            };
            callbacks.schedule(set_nonce_fn, stream)?;
        } else {
            let mut d_seed = context.alloc(STATE_SIZE, AllocationPlacement::BestFit)?;
            let mut d_nonce = context.alloc(1, AllocationPlacement::BestFit)?;
            memory_copy_async(&mut d_seed, unsafe { &seed_accessor.get().0 }, &stream)?;
            blake2s_pow(&d_seed, pow_bits, u64::MAX, &mut d_nonce[0], stream)?;
            memory_copy_async(
                slice::from_mut::<u64>(unsafe { nonce_accessor.get_mut() }),
                &d_nonce,
                &stream,
            )?;
        };
        let verify_fn = move || unsafe {
            Blake2sTranscript::verify_pow(seed_accessor.get_mut(), *nonce_accessor.get(), pow_bits);
        };
        callbacks.schedule(verify_fn, stream)?;
        Ok(Self { nonce })
    }
}
