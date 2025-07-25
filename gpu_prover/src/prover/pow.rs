use super::context::{HostAllocator, ProverContext};
use crate::allocator::tracker::AllocationPlacement;
use crate::blake2s::{blake2s_pow, STATE_SIZE};
use crate::prover::callbacks::Callbacks;
use blake2s_u32::BLAKE2S_DIGEST_SIZE_U32_WORDS;
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use prover::transcript::{Blake2sTranscript, Seed};
use std::ops::{Deref, DerefMut};
use std::slice;
use std::sync::{Arc, Mutex};

pub(crate) struct PowOutput {
    pub nonce: Arc<Mutex<Box<u64, HostAllocator>>>,
}

impl PowOutput {
    pub fn new<'a>(
        seed: Arc<Mutex<Seed>>,
        pow_bits: u32,
        external_nonce: Option<u64>,
        callbacks: &mut Callbacks<'a>,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        let mut nonce = Box::new_in(0u64, HostAllocator::default());
        let stream = context.get_exec_stream();
        if let Some(external_nonce) = external_nonce {
            *nonce = external_nonce;
        } else {
            let h_seed = Arc::new(Mutex::new(Box::new_in(
                [0u32; BLAKE2S_DIGEST_SIZE_U32_WORDS],
                HostAllocator::default(),
            )));
            let seed_clone = seed.clone();
            let h_seed_clone = h_seed.clone();
            let set_h_seed_fn = move || {
                h_seed_clone
                    .lock()
                    .unwrap()
                    .copy_from_slice(&seed_clone.lock().unwrap().0);
            };
            callbacks.schedule(set_h_seed_fn, stream)?;
            let mut d_seed = context.alloc(STATE_SIZE, AllocationPlacement::BestFit)?;
            let mut d_nonce = context.alloc(1, AllocationPlacement::BestFit)?;
            memory_copy_async(
                d_seed.deref_mut(),
                h_seed.lock().unwrap().deref().deref(),
                &stream,
            )?;
            blake2s_pow(&d_seed, pow_bits, u64::MAX, &mut d_nonce[0], stream)?;
            memory_copy_async(slice::from_mut(nonce.deref_mut()), &mut d_nonce, &stream)?;
        };
        let nonce = Arc::new(Mutex::new(nonce));
        let nonce_clone = nonce.clone();
        let verify_fn = move || {
            let nonce = *nonce_clone.lock().unwrap().deref().deref();
            Blake2sTranscript::verify_pow(&mut seed.lock().unwrap(), nonce, pow_bits);
        };
        callbacks.schedule(verify_fn, stream)?;
        Ok(Self { nonce })
    }
}
