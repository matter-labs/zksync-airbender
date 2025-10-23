#![feature(allocator_api)]
#![allow(incomplete_features)]
#![feature(generic_const_exprs)]

use std::alloc::Global;
use std::collections::HashMap;
use std::path::Path;

use cs::cs::oracle::ExecutorFamilyDecoderData;
use cs::machine::machine_configurations::pad_bytecode;
use cs::tables::TableDriver;
use definitions::MerkleTreeCap;
use merkle_trees::DefaultTreeConstructor;
use prover::fft::*;
use prover::field::*;
use prover::prover_stages::SetupPrecomputations;
use prover::tracers::delegation::bigint_with_control_factory_fn;
use prover::tracers::delegation::blake2_with_control_factory_fn;
use prover::tracers::delegation::keccak_special5_factory_fn;
use prover::tracers::oracles::delegation_oracle::DelegationCircuitOracle;
use prover::tracers::oracles::main_risc_v_circuit::MainRiscVOracle;
use prover::tracers::unrolled::tracer::MemTracingFamilyChunk;
use prover::tracers::unrolled::tracer::NonMemTracingFamilyChunk;
use prover::unrolled::MemoryCircuitOracle;
use prover::unrolled::NonMemoryCircuitOracle;
use prover::DEFAULT_TRACE_PADDING_MULTIPLE;
use prover::*;
use risc_v_simulator::cycle::IMStandardIsaConfig;
use risc_v_simulator::cycle::IMStandardIsaConfigWithUnsignedMulDiv;
use risc_v_simulator::cycle::IWithoutByteAccessIsaConfig;
use risc_v_simulator::cycle::IWithoutByteAccessIsaConfigWithDelegation;
use risc_v_simulator::cycle::MachineConfig;
use worker::Worker;

pub use bigint_with_control;
pub use blake2_with_compression;
pub use final_reduced_risc_v_machine;
pub use keccak_special5;
pub use machine_without_signed_mul_div;
pub use prover;
pub use reduced_risc_v_log_23_machine;
pub use reduced_risc_v_machine;
pub use risc_v_cycles;

pub mod circuits;
pub mod unrolled_circuits;
pub use self::circuits::*;
pub use self::unrolled_circuits::*;

pub fn pad_bytecode_for_proving(bytecode: &mut Vec<u32>) {
    pad_bytecode::<{ risc_v_cycles::MAX_ROM_SIZE as u32 }>(bytecode);
}

pub fn is_default_machine_configuration<C: MachineConfig>() -> bool {
    std::any::TypeId::of::<C>() == std::any::TypeId::of::<IMStandardIsaConfig>()
}

pub fn is_reduced_machine_configuration<C: MachineConfig>() -> bool {
    std::any::TypeId::of::<C>()
        == std::any::TypeId::of::<IWithoutByteAccessIsaConfigWithDelegation>()
}

pub fn is_machine_without_signed_mul_div_configuration<C: MachineConfig>() -> bool {
    std::any::TypeId::of::<C>() == std::any::TypeId::of::<IMStandardIsaConfigWithUnsignedMulDiv>()
}

pub fn is_final_reduced_machine_configuration<C: MachineConfig>() -> bool {
    std::any::TypeId::of::<C>() == std::any::TypeId::of::<IWithoutByteAccessIsaConfig>()
}

pub fn delegation_factories_for_machine<C: MachineConfig, A: GoodAllocator>() -> HashMap<
    u16,
    Box<dyn Fn() -> prover::tracers::delegation::DelegationWitness<A> + Send + Sync + 'static>,
> {
    if is_default_machine_configuration::<C>()
        || is_machine_without_signed_mul_div_configuration::<C>()
    {
        // blake, bigint and keccak
        HashMap::from_iter(
            [
                (
                    blake2_with_compression::DELEGATION_TYPE_ID as u16,
                    Box::new(|| {
                        blake2_with_control_factory_fn(
                            blake2_with_compression::DELEGATION_TYPE_ID as u16,
                            blake2_with_compression::NUM_DELEGATION_CYCLES,
                            A::default(),
                        )
                    })
                        as Box<
                            dyn Fn() -> prover::tracers::delegation::DelegationWitness<A>
                                + Send
                                + Sync
                                + 'static,
                        >,
                ),
                (
                    bigint_with_control::DELEGATION_TYPE_ID as u16,
                    Box::new(|| {
                        bigint_with_control_factory_fn(
                            bigint_with_control::DELEGATION_TYPE_ID as u16,
                            bigint_with_control::NUM_DELEGATION_CYCLES,
                            A::default(),
                        )
                    })
                        as Box<
                            dyn Fn() -> prover::tracers::delegation::DelegationWitness<A>
                                + Send
                                + Sync
                                + 'static,
                        >,
                ),
                (
                    keccak_special5::DELEGATION_TYPE_ID as u16,
                    Box::new(|| {
                        keccak_special5_factory_fn(
                            keccak_special5::DELEGATION_TYPE_ID as u16,
                            keccak_special5::NUM_DELEGATION_CYCLES,
                            A::default(),
                        )
                    })
                        as Box<
                            dyn Fn() -> prover::tracers::delegation::DelegationWitness<A>
                                + Send
                                + Sync
                                + 'static,
                        >,
                ),
            ]
            .into_iter(),
        )
    } else if is_reduced_machine_configuration::<C>() {
        // only blake
        HashMap::from_iter(
            [(
                blake2_with_compression::DELEGATION_TYPE_ID as u16,
                Box::new(|| {
                    blake2_with_control_factory_fn(
                        blake2_with_compression::DELEGATION_TYPE_ID as u16,
                        blake2_with_compression::NUM_DELEGATION_CYCLES,
                        A::default(),
                    )
                })
                    as Box<
                        dyn Fn() -> prover::tracers::delegation::DelegationWitness<A>
                            + Send
                            + Sync
                            + 'static,
                    >,
            )]
            .into_iter(),
        )
    } else if is_final_reduced_machine_configuration::<C>() {
        HashMap::new() // no delegations
    } else {
        panic!("unknown machine configuration {:?}", C::default())
    }
}

pub struct MainCircuitPrecomputations<C: MachineConfig, A: GoodAllocator, B: GoodAllocator = Global>
{
    pub compiled_circuit: cs::one_row_compiler::CompiledCircuitArtifact<Mersenne31Field>,
    pub table_driver: TableDriver<Mersenne31Field>,
    pub twiddles: Twiddles<Mersenne31Complex, A>,
    pub lde_precomputations: LdePrecomputations<A>,
    pub setup: SetupPrecomputations<DEFAULT_TRACE_PADDING_MULTIPLE, A, DefaultTreeConstructor>,
    pub witness_eval_fn_for_gpu_tracer: fn(&mut SimpleWitnessProxy<'_, MainRiscVOracle<'_, C, B>>),
}

pub enum UnrolledCircuitWitnessEvalFn<A: GoodAllocator> {
    NonMemory {
        witness_fn: fn(&'_ mut SimpleWitnessProxy<'_, NonMemoryCircuitOracle<'_>>),
        decoder_table: Vec<ExecutorFamilyDecoderData, A>,
        default_pc_value_in_padding: u32,
    },
    Memory {
        witness_fn: fn(&'_ mut SimpleWitnessProxy<'_, MemoryCircuitOracle<'_>>),
        decoder_table: Vec<ExecutorFamilyDecoderData, A>,
    },
    Unified {},
}

pub struct UnrolledCircuitPrecomputations<A: GoodAllocator, B: GoodAllocator = Global> {
    pub family_idx: u8,
    pub trace_len: usize,
    pub lde_factor: usize,
    pub tree_cap_size: usize,
    pub compiled_circuit: cs::one_row_compiler::CompiledCircuitArtifact<Mersenne31Field>,
    pub table_driver: TableDriver<Mersenne31Field>,
    pub twiddles: Twiddles<Mersenne31Complex, A>,
    pub lde_precomputations: LdePrecomputations<A>,
    pub setup: SetupPrecomputations<DEFAULT_TRACE_PADDING_MULTIPLE, A, DefaultTreeConstructor>,
    pub witness_eval_fn_for_gpu_tracer: Option<UnrolledCircuitWitnessEvalFn<B>>,
}

pub struct DelegationCircuitPrecomputations<A: GoodAllocator, B: GoodAllocator = Global> {
    pub trace_len: usize,
    pub lde_factor: usize,
    pub tree_cap_size: usize,
    pub compiled_circuit: DelegationProcessorDescription,
    pub twiddles: Twiddles<Mersenne31Complex, A>,
    pub lde_precomputations: LdePrecomputations<A>,
    pub setup: SetupPrecomputations<DEFAULT_TRACE_PADDING_MULTIPLE, A, DefaultTreeConstructor>,
    pub witness_eval_fn_for_gpu_tracer:
        fn(&mut SimpleWitnessProxy<'_, DelegationCircuitOracle<'_, B>>),
}

pub fn get_delegation_compiled_circuits_for_machine_type<C: MachineConfig>(
) -> Vec<(u32, DelegationProcessorDescription)> {
    if is_default_machine_configuration::<C>() {
        get_delegation_compiled_circuits_for_default_machine()
    } else if is_reduced_machine_configuration::<C>() {
        get_delegation_compiled_circuits_for_reduced_machine()
    } else if is_final_reduced_machine_configuration::<C>() {
        vec![]
    } else if is_machine_without_signed_mul_div_configuration::<C>() {
        get_delegation_compiled_circuits_for_machine_without_signed_mul_div_configuration()
    } else {
        panic!("unknown machine configuration {:?}", C::default())
    }
}

pub fn get_delegation_compiled_circuits_for_default_machine(
) -> Vec<(u32, DelegationProcessorDescription)> {
    let mut machines = vec![];
    machines.push((
        blake2_with_compression::DELEGATION_TYPE_ID as u32,
        blake2_with_compression::get_delegation_circuit(),
    ));
    machines.push((
        bigint_with_control::DELEGATION_TYPE_ID,
        bigint_with_control::get_delegation_circuit(),
    ));
    machines.push((
        keccak_special5::DELEGATION_TYPE_ID,
        keccak_special5::get_delegation_circuit(),
    ));

    assert_eq!(
        machines.len(),
        IMStandardIsaConfig::ALLOWED_DELEGATION_CSRS.len()
    );
    for i in 0..machines.len() {
        assert_eq!(
            machines[i].0,
            IMStandardIsaConfig::ALLOWED_DELEGATION_CSRS[i]
        );
    }

    machines
}

pub fn get_delegation_compiled_circuits_for_reduced_machine(
) -> Vec<(u32, DelegationProcessorDescription)> {
    let mut machines = vec![];
    machines.push((
        blake2_with_compression::DELEGATION_TYPE_ID as u32,
        blake2_with_compression::get_delegation_circuit(),
    ));

    assert_eq!(
        machines.len(),
        IWithoutByteAccessIsaConfigWithDelegation::ALLOWED_DELEGATION_CSRS.len()
    );
    for i in 0..machines.len() {
        assert_eq!(
            machines[i].0,
            IWithoutByteAccessIsaConfigWithDelegation::ALLOWED_DELEGATION_CSRS[i]
        );
    }

    machines
}

pub fn all_delegation_circuits_precomputations<A: GoodAllocator, B: GoodAllocator>(
    worker: &Worker,
) -> Vec<(u32, DelegationCircuitPrecomputations<A, B>)> {
    vec![
        (
            blake2_with_compression::DELEGATION_TYPE_ID,
            get_blake2_with_compression_circuit_setup(worker),
        ),
        (
            bigint_with_control::DELEGATION_TYPE_ID,
            get_bigint_with_control_circuit_setup(worker),
        ),
        (
            keccak_special5::DELEGATION_TYPE_ID,
            get_keccak_special5_circuit_setup(worker),
        ),
        // (
        //     poseidon2_compression_with_witness::DELEGATION_TYPE_ID,
        //     get_poseidon2_compress_with_witness_circuit_setup(worker),
        // ),
    ]
}

pub fn get_delegation_compiled_circuits_for_machine_without_signed_mul_div_configuration(
) -> Vec<(u32, DelegationProcessorDescription)> {
    let mut machines = vec![];
    machines.push((
        blake2_with_compression::DELEGATION_TYPE_ID as u32,
        blake2_with_compression::get_delegation_circuit(),
    ));
    machines.push((
        bigint_with_control::DELEGATION_TYPE_ID,
        bigint_with_control::get_delegation_circuit(),
    ));
    machines.push((
        keccak_special5::DELEGATION_TYPE_ID,
        keccak_special5::get_delegation_circuit(),
    ));

    assert_eq!(
        machines.len(),
        IMStandardIsaConfigWithUnsignedMulDiv::ALLOWED_DELEGATION_CSRS.len()
    );
    for i in 0..machines.len() {
        assert_eq!(
            machines[i].0,
            IMStandardIsaConfigWithUnsignedMulDiv::ALLOWED_DELEGATION_CSRS[i]
        );
    }

    machines
}

pub mod all_parameters {
    use verifier_common::prover::definitions::MerkleTreeCap;
    include!("../generated/all_delegation_circuits_params.rs");
}

pub const CAP_SIZE: usize = 64;
pub const NUM_COSETS: usize = 2;

pub type DelegationCircuitSetupParams = (u32, u32, [MerkleTreeCap<CAP_SIZE>; NUM_COSETS]);

#[derive(serde::Serialize, serde::Deserialize)]
pub struct UnrolledCircuitSetupParams {
    pub family_idx: u32,
    pub capacity: u32,
    #[serde(with = "serde_big_array::BigArray")]
    #[serde(bound(deserialize = "MerkleTreeCap<CAP_SIZE>: serde::Deserialize<'de>"))]
    #[serde(bound(serialize = "MerkleTreeCap<CAP_SIZE>: serde::Serialize"))]
    pub setup_caps: [MerkleTreeCap<CAP_SIZE>; NUM_COSETS],
}

#[derive(serde::Serialize, serde::Deserialize)]
pub struct InitsAndTeardownsCircuitSetupParams {
    #[serde(with = "serde_big_array::BigArray")]
    #[serde(bound(deserialize = "MerkleTreeCap<CAP_SIZE>: serde::Deserialize<'de>"))]
    #[serde(bound(serialize = "MerkleTreeCap<CAP_SIZE>: serde::Serialize"))]
    pub setup_caps: [MerkleTreeCap<CAP_SIZE>; NUM_COSETS],
}

fn make_factories_for_unrolled_circuits_impl<A: GoodAllocator>(
    non_mem_factories: &[fn() -> (
        u8,
        Box<dyn Fn() -> NonMemTracingFamilyChunk<A> + Send + Sync + 'static>,
    )],
    mem_factories: &[fn() -> (
        u8,
        Box<dyn Fn() -> MemTracingFamilyChunk<A> + Send + Sync + 'static>,
    )],
) -> (
    HashMap<u8, Box<dyn Fn() -> NonMemTracingFamilyChunk<A> + Send + Sync + 'static>>,
    HashMap<u8, Box<dyn Fn() -> MemTracingFamilyChunk<A> + Send + Sync + 'static>>,
) {
    let mut non_mem = HashMap::new();
    let mut mem = HashMap::new();

    for el in non_mem_factories.iter() {
        let (family, factory) = (el)();
        let existing = non_mem.insert(family, factory);
        assert!(existing.is_none());
    }

    for el in mem_factories.iter() {
        let (family, factory) = (el)();
        let existing = mem.insert(family, factory);
        assert!(existing.is_none());
    }

    (non_mem, mem)
}

pub fn factories_for_unrolled_circuits_base_layer<A: GoodAllocator>() -> (
    HashMap<u8, Box<dyn Fn() -> NonMemTracingFamilyChunk<A> + Send + Sync + 'static>>,
    HashMap<u8, Box<dyn Fn() -> MemTracingFamilyChunk<A> + Send + Sync + 'static>>,
) {
    let non_mem_fns = vec![
        ::add_sub_lui_auipc_mop::get_tracer_factory,
        ::jump_branch_slt::get_tracer_factory,
        ::shift_binary_csr::get_tracer_factory,
        ::mul_div::get_tracer_factory,
    ];
    let mem_fns = vec![
        ::load_store_word_only::get_tracer_factory,
        ::load_store_subword_only::get_tracer_factory,
    ];
    make_factories_for_unrolled_circuits_impl::<A>(&non_mem_fns, &mem_fns)
}

pub fn factories_for_unrolled_circuits_base_layer_unsigned_only<A: GoodAllocator>() -> (
    HashMap<u8, Box<dyn Fn() -> NonMemTracingFamilyChunk<A> + Send + Sync + 'static>>,
    HashMap<u8, Box<dyn Fn() -> MemTracingFamilyChunk<A> + Send + Sync + 'static>>,
) {
    let non_mem_fns = vec![
        ::add_sub_lui_auipc_mop::get_tracer_factory,
        ::jump_branch_slt::get_tracer_factory,
        ::shift_binary_csr::get_tracer_factory,
        ::mul_div_unsigned::get_tracer_factory,
    ];
    let mem_fns = vec![
        ::load_store_word_only::get_tracer_factory,
        ::load_store_subword_only::get_tracer_factory,
    ];
    make_factories_for_unrolled_circuits_impl::<A>(&non_mem_fns, &mem_fns)
}

pub fn factories_for_unrolled_circuits_recursion_layer<A: GoodAllocator>() -> (
    HashMap<u8, Box<dyn Fn() -> NonMemTracingFamilyChunk<A> + Send + Sync + 'static>>,
    HashMap<u8, Box<dyn Fn() -> MemTracingFamilyChunk<A> + Send + Sync + 'static>>,
) {
    let non_mem_fns = vec![
        ::add_sub_lui_auipc_mop::get_tracer_factory,
        ::jump_branch_slt::get_tracer_factory,
        ::shift_binary_csr::get_tracer_factory,
    ];
    let mem_fns = vec![::load_store_word_only::get_tracer_factory as _];
    make_factories_for_unrolled_circuits_impl::<A>(&non_mem_fns, &mem_fns[..])
}

pub fn compute_unrolled_circuits_params_for_machine_configuration<C: MachineConfig>(
    binary_image: &[u32],
    bytecode: &[u32],
) -> Vec<UnrolledCircuitSetupParams> {
    if is_default_machine_configuration::<C>() {
        compute_unrolled_circuits_params_base_layer(binary_image, bytecode)
    } else if is_machine_without_signed_mul_div_configuration::<C>() {
        compute_unrolled_circuits_params_base_layer_unsigned_only(binary_image, bytecode)
    } else if is_reduced_machine_configuration::<C>() {
        compute_unrolled_circuits_params_recursion_layer(binary_image, bytecode)
    } else {
        panic!("Unknown configuration {:?}", std::any::type_name::<C>());
    }
}

pub fn compute_unrolled_circuits_params_base_layer(
    binary_image: &[u32],
    bytecode: &[u32],
) -> Vec<UnrolledCircuitSetupParams> {
    let eval_fns = vec![
        add_sub_lui_auipc_mop_circuit_setup,
        jump_branch_slt_circuit_setup,
        shift_binary_csr_circuit_setup,
        mul_div_circuit_setup,
        load_store_word_only_circuit_setup,
        load_store_subword_only_circuit_setup,
    ];
    compute_unrolled_circuits_params_impl(binary_image, bytecode, &eval_fns)
}

pub fn compute_unrolled_circuits_params_base_layer_unsigned_only(
    binary_image: &[u32],
    bytecode: &[u32],
) -> Vec<UnrolledCircuitSetupParams> {
    let eval_fns = vec![
        add_sub_lui_auipc_mop_circuit_setup,
        jump_branch_slt_circuit_setup,
        shift_binary_csr_circuit_setup,
        mul_div_unsigned_circuit_setup,
        load_store_word_only_circuit_setup,
        load_store_subword_only_circuit_setup,
    ];
    compute_unrolled_circuits_params_impl(binary_image, bytecode, &eval_fns)
}

pub fn compute_unrolled_circuits_params_recursion_layer(
    binary_image: &[u32],
    bytecode: &[u32],
) -> Vec<UnrolledCircuitSetupParams> {
    let eval_fns = vec![
        add_sub_lui_auipc_mop_circuit_setup,
        jump_branch_slt_circuit_setup,
        shift_binary_csr_circuit_setup,
        load_store_word_only_circuit_setup,
    ];
    compute_unrolled_circuits_params_impl(binary_image, bytecode, &eval_fns)
}

fn compute_unrolled_circuits_params_impl(
    binary_image: &[u32],
    bytecode: &[u32],
    circuits: &[fn(&[u32], &[u32], &Worker) -> UnrolledCircuitPrecomputations<Global, Global>],
) -> Vec<UnrolledCircuitSetupParams> {
    assert!(binary_image.len() >= bytecode.len());
    assert!(binary_image.starts_with(bytecode));
    let worker = prover::worker::Worker::new();
    use prover::merkle_trees::MerkleTreeConstructor;

    let mut results = Vec::with_capacity(circuits.len());
    for eval_fn in circuits.iter() {
        let precomp = (eval_fn)(binary_image, bytecode, &worker);
        let num_cycles = (precomp.trace_len - 1) as u32;
        let setup = DefaultTreeConstructor::dump_caps(&precomp.setup.trees);
        let setup: [MerkleTreeCap<CAP_SIZE>; NUM_COSETS] = setup
            .into_iter()
            .map(|el| MerkleTreeCap {
                cap: el.cap.try_into().unwrap(),
            })
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        results.push(UnrolledCircuitSetupParams {
            family_idx: precomp.family_idx as u32,
            capacity: num_cycles,
            setup_caps: setup,
        });
    }
    // sort by family index
    results.sort_by(|a, b| a.family_idx.cmp(&b.family_idx));

    results
}

pub fn compute_inits_and_teardowns_params(
    binary_image: &[u32],
    bytecode: &[u32],
) -> [MerkleTreeCap<CAP_SIZE>; NUM_COSETS] {
    let worker = prover::worker::Worker::new();
    use prover::merkle_trees::MerkleTreeConstructor;
    let setup = crate::unrolled_circuits::inits_and_teardowns_circuit_setup::<Global, Global>(
        binary_image,
        bytecode,
        &worker,
    );
    let setup = DefaultTreeConstructor::dump_caps(&setup.setup.trees);
    let setup: [MerkleTreeCap<CAP_SIZE>; NUM_COSETS] = setup
        .into_iter()
        .map(|el| MerkleTreeCap {
            cap: el.cap.try_into().unwrap(),
        })
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();

    setup
}

pub fn compute_delegation_circuits_params() -> Vec<DelegationCircuitSetupParams> {
    let worker = prover::worker::Worker::new();
    use prover::merkle_trees::MerkleTreeConstructor;
    let all_circuits = all_delegation_circuits_precomputations::<Global, Global>(&worker);
    let mut results = Vec::with_capacity(all_circuits.len());
    for (delegation_type, prec) in all_circuits.into_iter() {
        let delegation_type = delegation_type as u32;
        let num_delegation_requests = (prec.trace_len - 1) as u32;
        let setup = DefaultTreeConstructor::dump_caps(&prec.setup.trees);
        let setup: [MerkleTreeCap<CAP_SIZE>; NUM_COSETS] = setup
            .into_iter()
            .map(|el| MerkleTreeCap {
                cap: el.cap.try_into().unwrap(),
            })
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();
        results.push((delegation_type, num_delegation_requests, setup));
    }

    results
}

pub fn generate_delegation_circuits_artifacts() -> String {
    use prover::cap_holder::array_to_tokens;
    use quote::quote;

    let all_params = compute_delegation_circuits_params();

    let mut streams = Vec::with_capacity(all_params.len());

    for (delegation_type, num_delegation_requests, setup) in all_params.into_iter() {
        let caps_stream = array_to_tokens(&setup);
        let t = quote! {
            (
                #delegation_type,
                #num_delegation_requests,
                #caps_stream
            )
        };
        streams.push(t);
    }

    use quote::TokenStreamExt;

    let mut full_stream = proc_macro2::TokenStream::new();
    full_stream.append_separated(
        streams.into_iter().map(|el| {
            quote! { #el }
        }),
        quote! {,},
    );

    let cap_size = CAP_SIZE;
    let num_cosets = NUM_COSETS;

    let description = quote! {
        pub const ALL_DELEGATION_CIRCUITS_PARAMS: &[(u32, u32, [MerkleTreeCap<#cap_size>; #num_cosets])] = & [#full_stream];
    }.to_string();

    description
}

pub fn read_binary(path: &Path) -> (Vec<u8>, Vec<u32>) {
    use std::io::Read;
    let mut file = std::fs::File::open(path).expect("must open provided file");
    let mut buffer = vec![];
    file.read_to_end(&mut buffer).expect("must read the file");
    assert_eq!(buffer.len() % core::mem::size_of::<u32>(), 0);
    let mut binary = Vec::with_capacity(buffer.len() / core::mem::size_of::<u32>());
    for el in buffer.as_chunks::<4>().0 {
        binary.push(u32::from_le_bytes(*el));
    }

    (buffer, binary)
}

pub fn compute_and_save_params(
    binary_image_path: &Path,
    bytecode_path: &Path,
    destination: &Path,
    gen_fn: fn(&[u32], &[u32]) -> Vec<UnrolledCircuitSetupParams>,
) {
    use sha3::Digest;
    let (raw_binary_image, binary_image) = read_binary(binary_image_path);
    let (raw_bytecode, bytecode) = read_binary(bytecode_path);
    let setups = (gen_fn)(&binary_image, &bytecode);
    let inits_setup = compute_inits_and_teardowns_params(&binary_image, &bytecode);
    let binary_image_hash = sha3::Keccak256::digest(&raw_binary_image);
    let bytecode_hash = sha3::Keccak256::digest(&raw_bytecode);
    let path = destination.join(format!(
        "{}_{}.json",
        hex::encode(binary_image_hash),
        hex::encode(bytecode_hash)
    ));
    let file = std::fs::File::create(path).expect("create result file");
    serde_json::to_writer(file, &(setups, inits_setup)).expect("must serialize");
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn generate_all() {
        let description = generate_delegation_circuits_artifacts();

        let mut dst = std::fs::File::create("generated/all_delegation_circuits_params.rs").unwrap();
        use std::io::Write;
        dst.write_all(&description.as_bytes()).unwrap();
    }

    #[test]
    fn test_generate_unrolled_base() {
        compute_and_save_params(
            Path::new("../../examples/basic_fibonacci/app.bin"),
            Path::new("../../examples/basic_fibonacci/app.text"),
            Path::new("./"),
            compute_unrolled_circuits_params_base_layer_unsigned_only,
        );
    }
}
