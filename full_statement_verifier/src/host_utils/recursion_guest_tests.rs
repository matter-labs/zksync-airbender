use super::fixture_artifact::ChainArtifact;
use super::{canonical_fsv_dir, fsv_stream, load_fsv_exact, VerifiedFsvProgram};
use common_constants::rom::ROM_SECOND_WORD_BITS;
use riscv_transpiler::abstractions::non_determinism::QuasiUARTSource;
use riscv_transpiler::ir::simple_instruction_set::preprocess_bytecode;
use riscv_transpiler::ir::ReducedMachineDecoderConfig;
use riscv_transpiler::jit::{
    Context, DefaultContextImpl, JitRunnerRam, JittedCode, MachineState, MemoryHolder, MopField,
    TraceChunk,
};
use riscv_transpiler::vm::{
    DelegationsAndFamiliesCounters, RamWithRomRegion, SimpleSnapshotter, SimpleTape, State, RAM, VM,
};
use std::ptr::NonNull;
use verifier_common::field::baby_bear::base::BabyBearField;
use verifier_common::fsv_binaries::{BlakeMode, FsvDescriptor, FsvProgram, SoundnessMode};

const RAM_CONFIG: JitRunnerRam = JitRunnerRam::Medium;

fn recursion_fixture() -> (VerifiedFsvProgram, Vec<u32>, [u32; 8]) {
    let mode = SoundnessMode::PessimisticConjecture;
    let artifact = ChainArtifact::load(mode, "unrolled");
    let descriptor = FsvDescriptor::new(
        mode,
        FsvProgram::UnrolledRecursionLayer,
        BlakeMode::Compression,
    );
    let guest = load_fsv_exact(canonical_fsv_dir(), &descriptor);
    let responses = fsv_stream(&artifact.setups, &artifact.proof, &descriptor);
    (guest, responses, artifact.chain_hash)
}

fn run_jit(
    guest: &VerifiedFsvProgram,
    responses: Vec<u32>,
    cycles_bound: Option<u32>,
) -> (MachineState, Box<MemoryHolder>, Box<TraceChunk>) {
    let mut source = QuasiUARTSource::new_with_reads(responses);
    let mut context = Context::new(DefaultContextImpl::new(&mut source), RAM_CONFIG);
    let mut memory = MemoryHolder::allocate_zeroed(RAM_CONFIG, Default::default());
    let mut trace = unsafe { Box::<TraceChunk>::new_zeroed().assume_init() };
    let instructions =
        preprocess_bytecode::<ReducedMachineDecoderConfig, false>(guest.unpadded_text());
    let jit = JittedCode::preprocess_bytecode(
        &instructions,
        cycles_bound,
        MopField::BabyBear,
        RAM_CONFIG,
    );
    jit.run(
        &mut context,
        &mut memory,
        NonNull::from(trace.as_mut()),
        guest.bin(),
    );
    (context.take_final_state().unwrap(), memory, trace)
}

#[test]
fn test_jit_recursive_verifier() {
    let (guest, responses, chain_hash) = recursion_fixture();
    let (state, _, _) = run_jit(&guest, responses, None);
    assert_eq!(state.materialized_registers()[18..26], chain_hash);
}

#[test]
fn test_ensure_proof_correctness() {
    let (guest, responses, chain_hash) = recursion_fixture();
    let instructions =
        preprocess_bytecode::<ReducedMachineDecoderConfig, true>(guest.unpadded_text());
    let tape = SimpleTape::new(&instructions);
    let mut ram = RamWithRomRegion::<ROM_SECOND_WORD_BITS>::from_rom_content(
        guest.bin(),
        RAM_CONFIG.ram_size(),
    );
    let mut source = QuasiUARTSource::new_with_reads(responses);
    let mut state = State::initial_with_counters(DelegationsAndFamiliesCounters::default());

    let finished = VM::<DelegationsAndFamiliesCounters>::run_basic_unrolled::<_, _, _, BabyBearField>(
        &mut state,
        &mut ram,
        &mut (),
        &tape,
        1 << 24,
        &mut source,
    );
    assert!(finished);
    assert_eq!(
        std::array::from_fn::<_, 8, _>(|i| state.registers[18 + i].value),
        chain_hash
    );
}

#[test]
#[ignore = "long-running manual consistency test"]
fn run_recursion_and_compare() {
    let (guest, responses, _) = recursion_fixture();
    let instructions =
        preprocess_bytecode::<ReducedMachineDecoderConfig, true>(guest.unpadded_text());
    let tape = SimpleTape::new(&instructions);
    let mut previous_timestamp = 0;

    for cycles in (836_694..1 << 24).step_by(1 << 16) {
        let (jit_state, jit_ram, trace) = run_jit(&guest, responses.clone(), Some(cycles));
        if jit_state.timestamp == previous_timestamp {
            return;
        }
        previous_timestamp = jit_state.timestamp;

        let mut vm_ram = RamWithRomRegion::<ROM_SECOND_WORD_BITS>::from_rom_content(
            guest.bin(),
            RAM_CONFIG.ram_size(),
        );
        let mut vm_state = State::initial_with_counters(DelegationsAndFamiliesCounters::default());
        let mut snapshotter = SimpleSnapshotter::<_, ROM_SECOND_WORD_BITS>::new_with_cycle_limit(
            cycles as usize,
            vm_state,
        );
        let mut source = QuasiUARTSource::new_with_reads(responses.clone());
        VM::<DelegationsAndFamiliesCounters>::run_by_timestamp_bound::<_, _, _, BabyBearField>(
            &mut vm_state,
            &mut vm_ram,
            &mut snapshotter,
            &tape,
            jit_state.timestamp,
            &mut source,
        );
        assert_eq!(
            vm_state,
            jit_state.as_replayer_state(),
            "cycle bound {cycles}"
        );

        for (index, (&value, &timestamp)) in jit_ram
            .memory()
            .iter()
            .zip(jit_ram.timestamps())
            .enumerate()
        {
            let address = (index * size_of::<u32>()) as u32;
            assert_eq!(
                vm_ram.read_word(address, jit_state.timestamp),
                (timestamp, value),
                "RAM address {address:#x} at cycle bound {cycles}",
            );
        }

        let (values, timestamps) = trace.data();
        let vm_tail = &snapshotter.reads_buffer[snapshotter.reads_buffer.len() - values.len()..];
        for (index, ((&(value, (low, high)), &jit_value), &jit_timestamp)) in
            vm_tail.iter().zip(values).zip(timestamps).enumerate()
        {
            let timestamp = (u64::from(high) << 32) | u64::from(low);
            assert_eq!(
                (value, timestamp),
                (jit_value, jit_timestamp),
                "trace index {index} at cycle bound {cycles}"
            );
        }
    }

    panic!("recursive verifier did not finish within the cycle bound");
}
