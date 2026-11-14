use super::calibrate::{calibrate_trace, load_guest, CensusCalibration};
use super::plan::{plan_unrolled_stream, RegionPlan, Section, StreamPlan};
use super::{trace_verifier_prefix, Trace};
use full_statement_verifier::host_utils::build_unrolled_stream;
use full_statement_verifier::host_utils::cost_model::{riscv_order, CircuitId, DELEGATION_TYPES};
use full_statement_verifier::program_proof::ProgramProof;
use prover::gkr::prover::GKRProof;
use prover::merkle_trees::DefaultTreeConstructor;
use prover::tests::gkr::orchestration::canonical_fixtures::CanonicalCircuit;
use prover::tests::gkr::orchestration::common::hardcoded_external_challenges;
use setups::{Setups, UnrolledCircuitSetupParams};
use std::collections::BTreeMap;
use verifier_common::cs::gkr_compiler::GKRCircuitArtifact;
use verifier_common::cs::utils::split_timestamp;
use verifier_common::field::baby_bear::{base::BabyBearField as BF, ext4::BabyBearExt4 as E4};
use verifier_common::fsv_binaries::{BlakeMode, FsvDescriptor, FsvProgram, SoundnessMode};
use verifier_common::gkr::flatten::flatten_gkr_proof_for_nds;
use verifier_common::prover::definitions::{FinalRegisterValue, DEFAULT_CAP_SIZE};

const BLAKE: BlakeMode = BlakeMode::Compression;
type Proof = GKRProof<BF, E4, DefaultTreeConstructor>;

#[derive(Clone, Copy, Debug)]
pub enum Counts {
    Three,
    One,
    RiscvOnly,
    DelegationsOnly,
}

fn circuit_for(id: CircuitId) -> CanonicalCircuit {
    use common_constants::*;
    match id {
        CircuitId::InitsAndTeardowns => CanonicalCircuit::InitsAndTeardowns,
        CircuitId::Riscv(k) => [
            CanonicalCircuit::AddSubLuiAuipcMop,
            CanonicalCircuit::JumpBranchSlt,
            CanonicalCircuit::ShiftBinop,
            CanonicalCircuit::UnsignedMulDiv,
            CanonicalCircuit::MemWordOnly,
            CanonicalCircuit::MemSubwordOnly,
        ]
        .into_iter()
        .find(|circuit| circuit.family_index().map(u32::from) == Some(k))
        .unwrap(),
        CircuitId::Delegation(k) => match k {
            BLAKE2S_DELEGATION_CSR_REGISTER => CanonicalCircuit::Blake2WithExtendedControl,
            BIGINT_OPS_WITH_CONTROL_CSR_REGISTER => CanonicalCircuit::BigintWithExtendedControl,
            KECCAK_SPECIAL5_CSR_REGISTER => CanonicalCircuit::KeccakSpecial5,
            KECCAK_COLUMN_PARITY_CSR_REGISTER => CanonicalCircuit::KeccakColumnParity,
            KECCAK_THETA_RHO_CSR_REGISTER => CanonicalCircuit::KeccakThetaRho,
            KECCAK_CHI5_CSR_REGISTER => CanonicalCircuit::KeccakChi5,
            _ => unreachable!(),
        },
    }
}

fn load(mode: SoundnessMode, id: CircuitId) -> (Proof, GKRCircuitArtifact<BF>) {
    let circuit = circuit_for(id);
    let root = proof_fixtures::root();
    let proof: Proof = proof_fixtures::read_file(circuit.proof_path(&root, mode));
    assert_eq!(
        proof.whir_proof.whir_schedule,
        circuit.prover_config(&root, mode).whir_schedule
    );
    let external = hardcoded_external_challenges();
    assert_eq!(
        proof
            .external_challenges
            .permutation_argument_linearization_challenges,
        external.permutation_argument_linearization_challenges
    );
    assert_eq!(
        proof.external_challenges.permutation_argument_additive_part,
        external.permutation_argument_additive_part
    );
    (proof, circuit.compiled_circuit(&root))
}

fn delegation_parameters(
    mode: SoundnessMode,
) -> &'static [verifier_common::DelegationCircuitSetupData<DEFAULT_CAP_SIZE>] {
    match mode {
        SoundnessMode::PessimisticConjecture => &full_statement_verifier::delegation_circuits_setups::pessimistic_conjecture::DELEGATION_CIRCUITS_SETUP_PARAMS,
        SoundnessMode::EthproofsSoundnessCalc => &full_statement_verifier::delegation_circuits_setups::ethproofs_soundcalc::DELEGATION_CIRCUITS_SETUP_PARAMS,
    }
}

fn append_region(
    stream: &mut Vec<u32>,
    regions: &mut Vec<RegionPlan>,
    circuit: CircuitId,
    section: Section,
    proofs: &[Proof],
    compiled: Option<&GKRCircuitArtifact<BF>>,
) {
    let count_word = stream.len();
    stream.push(proofs.len().try_into().unwrap());
    let mut first_words = Vec::new();
    for proof in proofs {
        first_words.push(stream.len());
        stream.extend(flatten_gkr_proof_for_nds(proof, compiled.unwrap(), BLAKE));
    }
    regions.push(RegionPlan {
        circuit,
        section,
        count_word,
        end_word: stream.len(),
        proof_first_words: first_words,
        closes_at_epilogue: false,
    });
}

pub fn stream(mode: SoundnessMode, program: FsvProgram, counts: Counts) -> (Vec<u32>, StreamPlan) {
    let (riscv_copies, delegation_copies) = match counts {
        Counts::Three => (3, 3),
        Counts::One => (1, 1),
        Counts::RiscvOnly => (3, 0),
        Counts::DelegationsOnly => (0, 3),
    };
    let mut proof = ProgramProof {
        riscv_proofs: BTreeMap::new(),
        compiled_riscv_circuits: BTreeMap::new(),
        inits_and_teardown_proofs: Vec::new(),
        inits_and_teardowns_circuit: None,
        delegation_proofs: BTreeMap::new(),
        compiled_delegation_circuits: BTreeMap::new(),
        register_final_values: vec![
            FinalRegisterValue {
                value: 0,
                last_access_timestamp: 0
            };
            32
        ],
        final_pc: 0,
        final_timestamp: common_constants::INITIAL_TIMESTAMP,
        end_params: [0; 8],
        recursion_chain_preimage: None,
        recursion_chain_hash: None,
        pow_challenge: 0,
        num_it_circuits: None,
    };
    let mut setups = Setups::new();
    let mut total_cycles = 0u64;
    for &family in riscv_order(program) {
        let (canonical, compiled) = load(mode, CircuitId::Riscv(family));
        total_cycles += riscv_copies as u64 * compiled.trace_len as u64;
        setups.insert(
            family,
            UnrolledCircuitSetupParams {
                family_idx: family,
                capacity: compiled.trace_len.try_into().unwrap(),
                setup_caps: canonical.whir_proof.setup_commitment.commitment.cap.clone(),
            },
        );
        proof
            .riscv_proofs
            .insert(family, vec![canonical; riscv_copies]);
        proof.compiled_riscv_circuits.insert(family, compiled);
    }
    assert!(total_cycles < full_statement_verifier::MAX_CYCLES);
    assert!(setups
        .keys()
        .copied()
        .eq(riscv_order(program).iter().copied()));
    let (inits, compiled) = load(mode, CircuitId::InitsAndTeardowns);
    assert!(!inits.inits_and_teardowns_top_bits.is_empty());
    assert!(inits
        .inits_and_teardowns_top_bits
        .windows(2)
        .all(|pair| pair[0] < pair[1]));
    proof.inits_and_teardown_proofs.push(inits);
    proof.inits_and_teardowns_circuit = Some(compiled);
    let mut permutation_elements = total_cycles << 2;
    for &delegation in DELEGATION_TYPES {
        if program == FsvProgram::UnrolledRecursionLayer
            && delegation != common_constants::BLAKE2S_DELEGATION_CSR_REGISTER
        {
            continue;
        }
        let (canonical, compiled) = load(mode, CircuitId::Delegation(delegation));
        let parameters = delegation_parameters(mode)
            .iter()
            .find(|entry| entry.delegation_type == delegation)
            .unwrap();
        assert_eq!(
            parameters.setup_cap.cap.as_slice(),
            canonical
                .whir_proof
                .setup_commitment
                .commitment
                .cap
                .cap
                .as_slice()
        );
        permutation_elements +=
            delegation_copies as u64 * parameters.num_permutation_terms_per_circuit as u64;
        proof
            .delegation_proofs
            .insert(delegation, vec![canonical; delegation_copies]);
        proof
            .compiled_delegation_circuits
            .insert(delegation, compiled);
    }
    assert!(permutation_elements < 1u64 << verifier_common::MAX_PERMUTATION_ELEMENTS_LOG2);

    let mut stream = Vec::new();
    for parameters in setups.values() {
        parameters.setup_caps.add_into_buffer(&mut stream);
    }
    for register in &proof.register_final_values {
        let (low, high) = split_timestamp(register.last_access_timestamp);
        stream.extend([register.value, low, high]);
    }
    let (low, high) = split_timestamp(proof.final_timestamp);
    stream.extend([proof.final_pc, low, high]);
    hardcoded_external_challenges().flatten_into_buffer(&mut stream);
    let mut regions = Vec::new();
    for &family in riscv_order(program) {
        append_region(
            &mut stream,
            &mut regions,
            CircuitId::Riscv(family),
            Section::Riscv,
            &proof.riscv_proofs[&family],
            Some(&proof.compiled_riscv_circuits[&family]),
        );
    }
    let inits_count_word = stream.len();
    append_region(
        &mut stream,
        &mut regions,
        CircuitId::InitsAndTeardowns,
        Section::InitsAndTeardowns,
        &proof.inits_and_teardown_proofs,
        proof.inits_and_teardowns_circuit.as_ref(),
    );
    for &delegation in DELEGATION_TYPES {
        append_region(
            &mut stream,
            &mut regions,
            CircuitId::Delegation(delegation),
            Section::Delegation,
            proof
                .delegation_proofs
                .get(&delegation)
                .map(Vec::as_slice)
                .unwrap_or(&[]),
            proof.compiled_delegation_circuits.get(&delegation),
        );
    }
    let pow_word = stream.len();
    regions.last_mut().unwrap().closes_at_epilogue = true;
    stream.extend([0, 0]);
    let plan = StreamPlan {
        regions,
        inits_count_word,
        pow_word,
        total_words: stream.len(),
    };
    if riscv_copies > 0 {
        assert_eq!(stream, build_unrolled_stream(&setups, &proof, BLAKE));
        assert_eq!(plan, plan_unrolled_stream(&setups, &proof, program));
    }
    (stream, plan)
}

pub fn trace(descriptor: &FsvDescriptor, counts: Counts) -> (Trace, StreamPlan) {
    assert_eq!(descriptor.blake, BLAKE);
    let (stream, plan) = stream(descriptor.soundness_mode, descriptor.program, counts);
    let (bin, text) = load_guest(descriptor);
    let trace = trace_verifier_prefix(&bin, &text, stream, plan.pow_word);
    assert_eq!(trace.marks.len(), plan.pow_word + 1);
    for region in &plan.regions {
        assert!(region.count_word < trace.marks.len());
        assert!(region.end_word < trace.marks.len());
        assert!(region
            .proof_first_words
            .iter()
            .all(|&word| word < trace.marks.len()));
    }
    (trace, plan)
}

pub fn calibration(descriptor: &FsvDescriptor, counts: Counts) -> CensusCalibration {
    let (trace, plan) = trace(descriptor, counts);
    calibrate_trace(&trace, &plan)
}

pub fn add_tail(
    cal: &mut CensusCalibration,
    tail: &full_statement_verifier::host_utils::cost_model::census::CensusVec,
) {
    for (total, tail) in cal.total.iter_mut().zip(tail) {
        *total += tail;
    }
}

pub fn fit(fixture: &super::fixtures::Fixture) -> super::calibrate::PooledCensus {
    use super::calibrate::{observed_spread, pool_census, pooled_prices, trace_fixture};
    let (chain_trace, chain_plan) = trace_fixture(fixture);
    let tail = core::array::from_fn(|d| {
        chain_trace.total_census[d] - chain_trace.census_marks[chain_plan.pow_word][d]
    });
    let chain = calibrate_trace(&chain_trace, &chain_plan);
    let mut main = calibration(&fixture.descriptor, Counts::Three);
    for region in &main.regions {
        match region.count {
            0 => assert!(region.spans.is_empty()),
            1 => {
                assert_eq!(region.circuit, CircuitId::InitsAndTeardowns);
                assert_eq!(region.spans.len(), 1);
            }
            3 => {
                assert_eq!(region.spans.len(), 2);
                assert_eq!(
                    region.spans[0], region.spans[1],
                    "{:?}: canonical interior spans differ",
                    region.circuit
                );
            }
            _ => unreachable!(),
        }
    }
    let prices = pooled_prices([&main]);
    let spread = observed_spread(std::slice::from_ref(&chain), &prices);
    add_tail(&mut main, &tail);
    pool_census(&[main, chain], prices, spread)
}
