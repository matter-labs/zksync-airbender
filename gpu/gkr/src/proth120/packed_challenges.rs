use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use era_cudart::slice::{DeviceSlice, DeviceVariable};
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::field::PR;
use gpu_core::primitives::static_host::{alloc_static_pinned_box_from_slice, StaticPinnedBox};
use gpu_hash::keccak256::{
    keccak256_pow, transcript_commit_initial_u32, transcript_draw_fields, DIGEST_WORDS,
};
use gpu_prover_context::ProverContext;

use crate::upstream::{
    lookup_challenges_pow_bits, lookup_identity_degree, split_timestamp, CommitmentMode,
    GKRCircuitArtifact, GKRExternalChallenges, ProverConfig, SecurityLevel,
};

pub const BOUNDARY_PREFIX_U32_LEN: usize = 32 * 3 + 3;
pub const PACKED_CHALLENGE_DRAWS: usize = GKRExternalChallenges::<PR, PR>::TOTAL_CHALLENGES + 2;

const EXTERNAL_CHALLENGES: usize = GKRExternalChallenges::<PR, PR>::TOTAL_CHALLENGES;

pub fn boundary_prefix_words(mode: &CommitmentMode) -> [u32; BOUNDARY_PREFIX_U32_LEN] {
    let CommitmentMode::MergedAndPackedMemoryAndWitness {
        register_final_state,
        final_pc,
        final_timestamp,
        ..
    } = mode
    else {
        panic!("packed_challenges: CommitmentMode::MergedAndPackedMemoryAndWitness required");
    };
    let mut words = [0u32; BOUNDARY_PREFIX_U32_LEN];
    for (reg_idx, register) in register_final_state.iter().enumerate() {
        let (timestamp_low, timestamp_high) = split_timestamp(register.last_access_timestamp);
        words[reg_idx * 3] = register.value;
        words[reg_idx * 3 + 1] = timestamp_low;
        words[reg_idx * 3 + 2] = timestamp_high;
    }
    let (final_timestamp_low, final_timestamp_high) = split_timestamp(*final_timestamp);
    words[96] = *final_pc;
    words[97] = final_timestamp_low;
    words[98] = final_timestamp_high;
    words
}

pub fn lookup_pow_bits(
    circuit: &GKRCircuitArtifact<PR>,
    security: SecurityLevel,
    external_challenges_pow_bits: u32,
) -> u32 {
    lookup_challenges_pow_bits(security.security_bits(), lookup_identity_degree(circuit))
        .max(external_challenges_pow_bits)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PackedChallengeConfig {
    pub pow_bits: u32,
    pub cap_log: u32,
    pub top_bits_len: usize,
    pub setup_present: bool,
}

impl PackedChallengeConfig {
    pub fn new(
        circuit: &GKRCircuitArtifact<PR>,
        config: &ProverConfig,
        mode: &CommitmentMode,
        setup_present: bool,
    ) -> Self {
        let CommitmentMode::MergedAndPackedMemoryAndWitness {
            external_challenges_pow_bits,
            ..
        } = mode
        else {
            panic!("packed_challenges: CommitmentMode::MergedAndPackedMemoryAndWitness required");
        };
        assert!(
            config.cap_size.is_power_of_two(),
            "packed_challenges: cap_size must be a power of two"
        );
        Self {
            pow_bits: lookup_pow_bits(
                circuit,
                config.security_level,
                *external_challenges_pow_bits,
            ),
            cap_log: config.cap_size.trailing_zeros(),
            top_bits_len: circuit.memory_layout.teardown_sets.len(),
            setup_present,
        }
    }
}

pub struct PackedChallenges {
    _prefix_host: StaticPinnedBox<u32>,
    nonce: DeviceAllocation<u64>,
    challenges: DeviceAllocation<PR>,
}

impl PackedChallenges {
    pub fn nonce(&self) -> &DeviceVariable<u64> {
        &self.nonce[0]
    }
    pub fn challenges(&self) -> &DeviceSlice<PR> {
        &self.challenges
    }
    pub fn external(&self) -> &DeviceSlice<PR> {
        &self.challenges[..EXTERNAL_CHALLENGES]
    }
    pub fn lookup(&self) -> &DeviceSlice<PR> {
        &self.challenges[EXTERNAL_CHALLENGES..]
    }
}

pub fn derive(
    seed: &mut DeviceSlice<u8>,
    mode: &CommitmentMode,
    inits_and_teardowns_top_bits: &DeviceSlice<u32>,
    setup_cap: &DeviceSlice<u32>,
    merged_cap: &DeviceSlice<u32>,
    cfg: &PackedChallengeConfig,
    context: &ProverContext,
) -> CudaResult<PackedChallenges> {
    let cap_words = 1usize
        .checked_shl(cfg.cap_log)
        .and_then(|cap| cap.checked_mul(DIGEST_WORDS))
        .expect("packed_challenges: cap length overflow");
    assert_eq!(
        inits_and_teardowns_top_bits.len(),
        cfg.top_bits_len,
        "packed_challenges: top_bits.len() == top_bits_len"
    );
    assert_eq!(
        setup_cap.len(),
        if cfg.setup_present { cap_words } else { 0 },
        "packed_challenges: setup_cap.len() == if setup_present {{ 8 << cap_log }} else {{ 0 }}"
    );
    assert_eq!(
        merged_cap.len(),
        cap_words,
        "packed_challenges: merged_cap.len() == 8 << cap_log"
    );
    let prefix_host = alloc_static_pinned_box_from_slice(&boundary_prefix_words(mode))?;
    let top_end = BOUNDARY_PREFIX_U32_LEN + cfg.top_bits_len;
    let setup_end = top_end + setup_cap.len();
    let mut words = context.alloc(setup_end + cap_words, AllocationPlacement::BestFit)?;
    let mut nonce = context.alloc(1, AllocationPlacement::BestFit)?;
    let mut challenges = context.alloc(PACKED_CHALLENGE_DRAWS, AllocationPlacement::BestFit)?;
    let stream = context.get_exec_stream();
    memory_copy_async(
        &mut words[..BOUNDARY_PREFIX_U32_LEN],
        &prefix_host[..],
        stream,
    )?;
    if !inits_and_teardowns_top_bits.is_empty() {
        memory_copy_async(
            &mut words[BOUNDARY_PREFIX_U32_LEN..top_end],
            inits_and_teardowns_top_bits,
            stream,
        )?;
    }
    if !setup_cap.is_empty() {
        memory_copy_async(&mut words[top_end..setup_end], setup_cap, stream)?;
    }
    memory_copy_async(&mut words[setup_end..], merged_cap, stream)?;
    transcript_commit_initial_u32(&words, seed, stream)?;
    keccak256_pow(seed, cfg.pow_bits, &mut nonce[0], stream)?;
    transcript_draw_fields(seed, &mut challenges, stream)?;
    drop(words);
    Ok(PackedChallenges {
        _prefix_host: prefix_host,
        nonce,
        challenges,
    })
}

pub fn split_challenges(
    challenges: &[PR; PACKED_CHALLENGE_DRAWS],
) -> (GKRExternalChallenges<PR, PR>, [PR; 2]) {
    (
        GKRExternalChallenges::from_slice(&challenges[..EXTERNAL_CHALLENGES]),
        [
            challenges[EXTERNAL_CHALLENGES],
            challenges[EXTERNAL_CHALLENGES + 1],
        ],
    )
}
