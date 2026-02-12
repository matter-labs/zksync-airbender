use super::callbacks::Callbacks;
use super::context::{HostAllocation, ProverContext};
use crate::allocator::tracker::AllocationPlacement;
use crate::blake2s::{blake2s_pow, STATE_SIZE};
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use prover::transcript::{Blake2sTranscript, Seed};
use std::slice;

pub(crate) fn search_pow_challenge<'a>(
    seed: &mut HostAllocation<Seed>,
    challenge: &mut HostAllocation<u64>,
    pow_bits: u32,
    external_challenge: Option<u64>,
    callbacks: &mut Callbacks<'a>,
    context: &ProverContext,
) -> CudaResult<()> {
    let stream = context.get_exec_stream();
    let challenge_accessor = challenge.get_mut_accessor();
    if pow_bits == 0 {
        // no PoW required
        let set_challenge_fn = move || unsafe {
            challenge_accessor.set(0);
        };
        callbacks.schedule(set_challenge_fn, stream)?;
    } else {
        let seed_accessor = seed.get_mut_accessor();
        if let Some(external_challenge) = external_challenge {
            let set_challenge_fn = move || unsafe {
                challenge_accessor.set(external_challenge);
            };
            callbacks.schedule(set_challenge_fn, stream)?;
        } else {
            let mut d_seed = context.alloc(STATE_SIZE, AllocationPlacement::BestFit)?;
            let mut d_challenge = context.alloc(1, AllocationPlacement::BestFit)?;
            memory_copy_async(&mut d_seed, unsafe { &seed_accessor.get().0 }, &stream)?;
            blake2s_pow(&d_seed, pow_bits, u64::MAX, &mut d_challenge[0], stream)?;
            memory_copy_async(
                slice::from_mut::<u64>(unsafe { challenge_accessor.get_mut() }),
                &d_challenge,
                &stream,
            )?;
        };
        let verify_fn = move || unsafe {
            Blake2sTranscript::verify_pow(
                seed_accessor.get_mut(),
                *challenge_accessor.get(),
                pow_bits,
            );
        };
        callbacks.schedule(verify_fn, stream)?;
    }
    Ok(())
}
