//! GPU numeric parity (HEAVY): the generated `add_sub_lui_auipc_mop` layer-0
//! forward kernel vs the CPU prover's `forward_loop::evaluate_layer` on a REAL
//! witness (a fully built `add_sub_lui_auipc_mop` GKR trace).
//!
//! This is the heavy companion to the LIGHT synthetic test in
//! `prover::gkr::forward::tests::generated_layer0_parity`. The light test
//! validates the CUDA codegen against a host replay of the same per-row
//! formulas on synthetic columns. Here we instead run the actual CPU prover
//! layer-0 forward evaluator (`evaluate_layer`) on a real witness and diff every
//! generated cache / inner-gate output against the CPU `GKRStorage` goldens.
//!
//! Wiring that matters:
//! - The kernel reads memory + witness base columns AND the vectorized-lookup
//!   setup poly (`generic_lookup`, cache_ext offset 15). So `generic_lookup`
//!   must be the `preprocessed_generic_lookup` returned by
//!   `preprocess_generic_lookups`, with `generic_lookup_len` = its length, so the
//!   GPU zero-pad gather matches the CPU `VectorizedLookupSetup` materialization.
//! - `setup` is never read by the layer-0 kernel body, so a 1-col zero buffer.
//! - Ext caches live at `Cached{layer:0, offset}` and base caches at the same
//!   address but in base field; inner gate outputs at `InnerLayer{layer:1, off}`.
//!   The CPU `GKRStorage::get_ext_poly` only resolves `InnerLayer`, so the ext
//!   caches are read with `try_get_ext_poly(..).unwrap()`.

use std::ffi::c_void;
use std::ptr;

use super::*;

use era_cudart::execution::KernelFunction;
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResultWrap;
use era_cudart::slice::DeviceSlice;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use era_cudart_sys::cudaGetSymbolAddress;

use crate::allocator::tracker::AllocationPlacement;
use crate::primitives::context::DeviceAllocation;
use crate::primitives::field::{BF, E4};
use crate::prover::gkr::forward::kernels::gkr_forward_launch_config;
use crate::prover::gkr::storage_layout::{address_storage_layer, GpuGKRStorageLayout};
use crate::prover::test_utils::make_test_context;
use crate::prover::ProverContext;

// Real-witness imports (test files are exempt from the `crate::upstream` rule).
use cs::definitions::{GKRAddress, NUM_PERMUTATION_ARGUMENT_KEY_PARTS};
use fft::materialize_powers_serial_starting_with_elem;
use prover::gkr::prover::forward_loop;

// Trace-size knob. The generated layer-0 body is trace-len agnostic (pure
// column-major per-row), and `evaluate_layer` for layer 0 just materializes the
// caches/gates per row, so a small power-of-two keeps the run fast. The circuit
// compiler asserts (a) `trace_len_log2 >= TIMESTAMP_COLUMNS_NUM_BITS` (= 19) and
// (b) the merged lookup/decoder tables (here `max_bytecode_size_in_words = 1<<20`)
// fit in one trace, i.e. `trace_len >= 1<<20`. So 20 is the smallest legal size,
// far cheaper than stagewise's 24.
const TRACE_LEN_LOG2: usize = 20;

// ---------------------------------------------------------------------------
// Rust mirror of the native `GkrFwdProxy<E>` (gkr_forward_generation.cuh) —
// copied verbatim from the LIGHT test. #[repr(C)], column-major data buffers
// only (challenges live in __constant__ tables).
// ---------------------------------------------------------------------------
#[repr(C)]
struct GpuGkrFwdProxy<E> {
    memory: *const BF,
    witness: *const BF,
    setup: *const BF,
    generic_lookup: *const E,
    generic_lookup_len: u32,
    cache_base: *mut BF,
    cache_ext: *mut E,
    out_base: *mut BF,
    out_ext: *mut E,
    trace_len: u32,
    perm_challenges: [E; 8],
    perm_additive: E,
    decoder_fill_value: *const E,
}

impl<E: Copy> Copy for GpuGkrFwdProxy<E> {}
impl<E: Copy> Clone for GpuGkrFwdProxy<E> {
    fn clone(&self) -> Self {
        *self
    }
}
// SAFETY: raw device pointers passed by value into a grid-constant kernel arg;
// the test keeps the backing allocations alive across the launch + sync.
unsafe impl<E> Send for GpuGkrFwdProxy<E> {}
unsafe impl<E> Sync for GpuGkrFwdProxy<E> {}

cuda_kernel_signature_arguments_and_function!(
    GpuGkrFwdAddSubLayer0<T>,
    proxy: GpuGkrFwdProxy<T>,
    count: u32,
);
cuda_kernel_declaration!(
    ab_gkr_forward_add_sub_lui_auipc_mop_layer0_kernel(proxy: GpuGkrFwdProxy<E4>, count: u32)
);

// ---------------------------------------------------------------------------
// Shared __constant__ challenge tables (gamma / alpha powers, defined in
// flat_layer.cu / setup/kernels.cu). We set them directly from host values. The
// forward-generation-specific perm challenges + decoder fill value now ride in
// the kernel proxy (by value / by pointer), not __constant__.
// ---------------------------------------------------------------------------
extern "C" {
    static ab_gkr_lookup_gamma_consts: [E4; 3];
    static ab_gkr_lookup_alpha_powers: [E4; 10];
}

fn set_const_e4(symbol: *const c_void, values: &[E4], context: &ProverContext) {
    let mut device_ptr: *mut c_void = ptr::null_mut();
    // SAFETY: `symbol` is the address of a valid __constant__ E4[/array] defined
    // in the linked archive.
    unsafe { cudaGetSymbolAddress(&mut device_ptr, symbol) }
        .wrap()
        .expect("cudaGetSymbolAddress failed");
    // SAFETY: the constant storage holds at least `values.len()` E4 elements.
    let slice = unsafe { DeviceSlice::from_raw_parts_mut(device_ptr as *mut E4, values.len()) };
    memory_copy_async(slice, values, context.get_exec_stream()).unwrap();
}

/// Upload a column-major matrix (`cols` columns, each `trace_len` long) as one
/// contiguous `[col*trace_len + row]` device allocation.
fn upload_columns(
    columns: &[Vec<BF>],
    trace_len: usize,
    context: &ProverContext,
) -> DeviceAllocation<BF> {
    let mut flat = Vec::with_capacity(columns.len() * trace_len);
    for col in columns {
        assert_eq!(col.len(), trace_len);
        flat.extend_from_slice(col);
    }
    let mut device = context.alloc(flat.len(), AllocationPlacement::Top).unwrap();
    memory_copy_async(&mut device, &flat[..], context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    device
}

fn zeroed_ext(cols: usize, trace_len: usize, context: &ProverContext) -> DeviceAllocation<E4> {
    let host = vec![E4::ZERO; cols * trace_len];
    let mut device = context.alloc(host.len(), AllocationPlacement::Top).unwrap();
    memory_copy_async(&mut device, &host[..], context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    device
}

fn zeroed_base(cols: usize, trace_len: usize, context: &ProverContext) -> DeviceAllocation<BF> {
    let host = vec![BF::ZERO; cols * trace_len];
    let mut device = context.alloc(host.len(), AllocationPlacement::Top).unwrap();
    memory_copy_async(&mut device, &host[..], context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    device
}

fn read_ext(device: &DeviceAllocation<E4>, context: &ProverContext) -> Vec<E4> {
    let mut host = vec![E4::ZERO; device.len()];
    memory_copy_async(&mut host, device, context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    host
}

fn read_base(device: &DeviceAllocation<BF>, context: &ProverContext) -> Vec<BF> {
    let mut host = vec![BF::ZERO; device.len()];
    memory_copy_async(&mut host, device, context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    host
}

fn e_mul(a: E4, b: E4) -> E4 {
    let mut x = a;
    x.mul_assign(&b);
    x
}

#[test]
#[cfg(not(no_cuda))]
#[serial]
#[ignore]
fn generated_forward_layer0_matches_cpu_evaluate_layer_real_witness() {
    type CountersT = DelegationsAndFamiliesCounters;

    const NUM_CYCLES_PER_CHUNK: usize = 1 << TRACE_LEN_LOG2;
    let trace_len: usize = 1 << TRACE_LEN_LOG2;
    let worker = Worker::new_with_num_threads(8);

    // ----- load program (same artifact + reads as stagewise) -----
    let binary = std::fs::read(test_artifact_path("examples/hashed_fibonacci/app.bin")).unwrap();
    assert_eq!(binary.len() % 4, 0);
    let binary: Vec<_> = binary
        .as_chunks::<4>()
        .0
        .into_iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect();

    let text_section =
        std::fs::read(test_artifact_path("examples/hashed_fibonacci/app.text")).unwrap();
    assert_eq!(text_section.len() % 4, 0);
    let text_section: Vec<_> = text_section
        .as_chunks::<4>()
        .0
        .into_iter()
        .map(|el| u32::from_le_bytes(*el))
        .collect();

    let instructions: Vec<Instruction> =
        preprocess_bytecode::<FullUnsignedMachineDecoderConfig, true>(&text_section);

    let tape = SimpleTape::new(&instructions);
    let mut ram = RamWithRomRegion::<{ ROM_SECOND_WORD_BITS }>::from_rom_content(&binary, 1 << 30);
    let cycles_bound = 1 << 20;

    let mut state = State::initial_with_counters(CountersT::default());
    let mut snapshotter =
        SimpleSnapshotter::<CountersT, { ROM_SECOND_WORD_BITS }>::new_with_cycle_limit(
            cycles_bound,
            state,
        );
    let mut non_determinism = QuasiUARTSource::new_with_reads(vec![15, 1]);

    let is_program_finished = VM::<CountersT>::run_basic_unrolled::<_, _, _, BF>(
        &mut state,
        &mut ram,
        &mut snapshotter,
        &tape,
        cycles_bound,
        &mut non_determinism,
    );
    assert!(is_program_finished);

    let counters = snapshotter.snapshots.last().unwrap().state.counters;

    let mut expected_final_state = state;
    expected_final_state.counters = Default::default();

    // ----- external challenges (fixed; matched on both sides) -----
    let memory_argument_alpha =
        E4::from_array_of_base([BF::new(2), BF::new(5), BF::new(42), BF::new(123)]);
    let permutation_argument_additive_part =
        E4::from_array_of_base([BF::new(7), BF::new(11), BF::new(1024), BF::new(8000)]);

    let permutation_argument_linearization_challenges: [E4; NUM_PERMUTATION_ARGUMENT_KEY_PARTS
        - 1] = materialize_powers_serial_starting_with_elem::<_, Global>(
        memory_argument_alpha,
        NUM_PERMUTATION_ARGUMENT_KEY_PARTS - 1,
    )
    .try_into()
    .unwrap();

    let external_challenges: GKRExternalChallenges<BF, E4> = GKRExternalChallenges {
        permutation_argument_linearization_challenges,
        permutation_argument_additive_part,
        _marker: std::marker::PhantomData,
    };

    // Arbitrary fixed lookup challenges (no transcript needed).
    let lookup_alpha = E4::from_array_of_base([BF::new(3), BF::new(9), BF::new(27), BF::new(81)]);
    let lookup_additive_part =
        E4::from_array_of_base([BF::new(13), BF::new(17), BF::new(19), BF::new(23)]);

    // ----- preprocess memory + build the real witness trace -----
    let preprocessing_data = process_binary_into_separate_tables_ext::<
        BF,
        FullUnsignedMachineDecoderConfig,
        true,
        Global,
    >(
        &text_section,
        &opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization(),
        1 << 20,
        &[
            NON_DETERMINISM_CSR as u16,
            BLAKE2S_DELEGATION_CSR_REGISTER as u16,
            BIGINT_OPS_WITH_CONTROL_CSR_REGISTER as u16,
            KECCAK_SPECIAL5_CSR_REGISTER as u16,
        ],
    );

    let add_sub_circuit = compile_unrolled_circuit_state_transition_into_gkr::<BF>(
        &|cs| add_sub_lui_auipc_mop_table_addition_fn(cs),
        &|cs| add_sub_lui_auipc_mop_circuit_with_preprocessed_bytecode_for_gkr(cs),
        1 << 20,
        TRACE_LEN_LOG2,
    );
    assert_eq!(add_sub_circuit.trace_len, trace_len);

    // The generated kernel stores each output at its storage-layout `poly_idx`
    // column (the prover passes the consolidated backing base pointers, with no
    // scatter). This standalone test wires its own scratch buffers, so read each
    // output column at the SAME `poly_idx` the generator emitted — derived from
    // the same `from_artifact` mapping the generator and prover use.
    let layout = GpuGKRStorageLayout::from_artifact(&add_sub_circuit);
    let poly_idx_of = |addr: GKRAddress| -> usize {
        layout
            .lookup(address_storage_layer(addr), &addr)
            .unwrap_or_else(|| panic!("output {addr:?} missing from layout"))
            .3 as usize
    };

    let num_calls =
        counters.get_calls_to_circuit_family::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX>();

    // Replay to populate the non-memory tracing buffer.
    let mut state = snapshotter.initial_snapshot.state;
    let mut ram_log_buffers = snapshotter
        .reads_buffer
        .make_range(0..snapshotter.reads_buffer.len());
    let mut ram = ReplayerRam::<{ ROM_SECOND_WORD_BITS }> {
        ram_log: &mut ram_log_buffers,
    };
    let mut buffer = vec![NonMemoryOpcodeTracingDataWithTimestamp::default(); num_calls];
    let mut buffers = vec![&mut buffer[..]];
    let mut tracer = NonMemDestinationHolder::<ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX> {
        buffers: &mut buffers[..],
    };
    ReplayerVM::<CountersT>::replay_basic_unrolled::<_, _, BF>(
        &mut state,
        &mut ram,
        &tape,
        &mut (),
        cycles_bound,
        &mut tracer,
    );
    assert_eq!(expected_final_state, state);

    let decoder_table_data = &preprocessing_data[&ADD_SUB_LUI_AUIPC_MOP_CIRCUIT_FAMILY_IDX];
    let witness_gen_data = decoder_table_data
        .iter()
        .map(|entry| entry.unwrap_or_default())
        .collect_vec();

    let oracle = NonMemoryCircuitOracle {
        inner: &buffer[..],
        decoder_table: &witness_gen_data,
        default_pc_value_in_padding: 4,
    };

    let mut full_trace = evaluate_gkr_witness_for_executor_family::<BF, _, _, _>(
        &add_sub_circuit,
        add_sub_lui_auipc_mod::witness_eval_fn,
        NUM_CYCLES_PER_CHUNK,
        &oracle,
        &TableDriver::new(),
        &worker,
        Global,
        Global,
    );

    assert_eq!(full_trace.column_major_memory_trace[0].len(), trace_len);
    // Snapshot the real base columns BEFORE `evaluate_layer` drains them out of
    // `full_trace` into the CPU storage.
    let memory_columns: Vec<Vec<BF>> = full_trace.column_major_memory_trace.clone();
    let witness_columns: Vec<Vec<BF>> = full_trace.column_major_witness_trace.clone();

    // ----- CPU golden: run layer-0 forward evaluation -----
    let setup = CpuGKRSetup::construct(
        &TableDriver::new(),
        decoder_table_data,
        trace_len,
        &add_sub_circuit,
    );
    let mut gkr_storage = GKRStorage::<BF, E4>::default();
    insert_virtual_setup_polys_for_test(trace_len, &mut gkr_storage);
    let (preprocessed_generic_lookup, decoder_lookup_fill_value) = setup
        .preprocess_generic_lookups(
            &add_sub_circuit,
            lookup_alpha,
            trace_len,
            &mut gkr_storage,
            &worker,
        );

    forward_loop::evaluate_layer(
        0,
        &add_sub_circuit.layers[0],
        &mut gkr_storage,
        &add_sub_circuit,
        &external_challenges,
        &mut full_trace,
        &[],
        trace_len,
        &preprocessed_generic_lookup,
        lookup_alpha,
        lookup_additive_part,
        decoder_lookup_fill_value,
        &worker,
    );

    // ----- GPU side: set __constant__ tables and launch the kernel -----
    let context = make_test_context(64 * 1024, 1024);

    // gamma consts [g, g^2, 2g] with gamma = lookup_additive_part.
    let gamma = lookup_additive_part;
    let gamma_sq = e_mul(gamma, gamma);
    let two_gamma = {
        let mut x = gamma;
        x.add_assign(&gamma);
        x
    };
    let gamma_consts = [gamma, gamma_sq, two_gamma];

    // alpha powers [1, a, a^2, ...] with a = lookup_alpha.
    let mut alpha_powers = [E4::ONE; 10];
    for k in 1..10 {
        alpha_powers[k] = e_mul(alpha_powers[k - 1], lookup_alpha);
    }

    // perm challenges: native table is [E4; 8]; the linearization challenges
    // array is length NUM_PERMUTATION_ARGUMENT_KEY_PARTS-1 (6), zero-pad the tail.
    let mut perm = [E4::ZERO; 8];
    assert!(permutation_argument_linearization_challenges.len() <= perm.len());
    for (slot, challenge) in perm
        .iter_mut()
        .zip(permutation_argument_linearization_challenges.iter())
    {
        *slot = *challenge;
    }

    // Shared gamma/alpha tables stay in __constant__.
    set_const_e4(
        // SAFETY: address of the linked __constant__ symbol.
        unsafe { &ab_gkr_lookup_gamma_consts as *const _ as *const c_void },
        &gamma_consts,
        &context,
    );
    set_const_e4(
        unsafe { &ab_gkr_lookup_alpha_powers as *const _ as *const c_void },
        &alpha_powers,
        &context,
    );
    // perm challenges + additive ride in the proxy by value; the decoder fill
    // value rides by pointer, so upload it to a 1-element device allocation.
    let mut d_fill = context.alloc::<E4>(1, AllocationPlacement::Top).unwrap();
    memory_copy_async(
        &mut d_fill[..],
        &[decoder_lookup_fill_value],
        context.get_exec_stream(),
    )
    .unwrap();
    context.get_exec_stream().synchronize().unwrap();

    // Device buffers. The kernel reads memory + witness columns and the
    // vectorized-lookup setup poly (generic_lookup). `setup` is unused at layer 0.
    let d_memory = upload_columns(&memory_columns, trace_len, &context);
    let d_witness = upload_columns(&witness_columns, trace_len, &context);
    let d_setup = zeroed_base(1, trace_len, &context);

    let generic_lookup: &[E4] = &preprocessed_generic_lookup;
    let mut d_generic = context
        .alloc(generic_lookup.len().max(1), AllocationPlacement::Top)
        .unwrap();
    if !generic_lookup.is_empty() {
        memory_copy_async(
            &mut d_generic[..generic_lookup.len()],
            generic_lookup,
            context.get_exec_stream(),
        )
        .unwrap();
    }
    context.get_exec_stream().synchronize().unwrap();

    let mut d_cache_base = zeroed_base(14, trace_len, &context);
    let mut d_cache_ext = zeroed_ext(16, trace_len, &context);
    let mut d_out_base = zeroed_base(1, trace_len, &context); // unused at layer 0
    let mut d_out_ext = zeroed_ext(23, trace_len, &context);

    let proxy = GpuGkrFwdProxy::<E4> {
        memory: d_memory.as_ptr(),
        witness: d_witness.as_ptr(),
        setup: d_setup.as_ptr(),
        generic_lookup: d_generic.as_ptr(),
        generic_lookup_len: generic_lookup.len() as u32,
        cache_base: d_cache_base.as_mut_ptr(),
        cache_ext: d_cache_ext.as_mut_ptr(),
        out_base: d_out_base.as_mut_ptr(),
        out_ext: d_out_ext.as_mut_ptr(),
        trace_len: trace_len as u32,
        perm_challenges: perm,
        perm_additive: external_challenges.permutation_argument_additive_part,
        decoder_fill_value: d_fill.as_ptr(),
    };

    let config = gkr_forward_launch_config(trace_len as u32, &context);
    let args = GpuGkrFwdAddSubLayer0Arguments::new(proxy, trace_len as u32);
    GpuGkrFwdAddSubLayer0Function(ab_gkr_forward_add_sub_lui_auipc_mop_layer0_kernel)
        .launch(&config, &args)
        .unwrap();
    context.get_exec_stream().synchronize().unwrap();

    let cache_ext = read_ext(&d_cache_ext, &context);
    let cache_base = read_base(&d_cache_base, &context);
    let out_ext = read_ext(&d_out_ext, &context);

    // ----- diff against the CPU GKRStorage goldens -----
    // ext caches at Cached{layer:0, offset}, read at the kernel's `poly_idx`.
    for off in [0usize, 1, 2, 3, 4, 5, 6, 7, 14, 15] {
        let addr = GKRAddress::Cached {
            layer: 0,
            offset: off,
        };
        let pidx = poly_idx_of(addr);
        let golden = gkr_storage
            .try_get_ext_poly(addr)
            .unwrap_or_else(|| panic!("missing CPU ext cache poly for offset {off}"));
        assert_eq!(golden.len(), trace_len, "ext cache {off} length");
        for row in 0..trace_len {
            assert_eq!(
                cache_ext[pidx * trace_len + row],
                golden[row],
                "ext cache offset {off} (poly_idx {pidx}) row {row}"
            );
        }
    }

    // base caches at Cached{layer:0, offset}, read at the kernel's `poly_idx`.
    for off in [8usize, 9, 10, 11, 12, 13] {
        let addr = GKRAddress::Cached {
            layer: 0,
            offset: off,
        };
        let pidx = poly_idx_of(addr);
        let golden = gkr_storage
            .try_get_base_poly(addr)
            .unwrap_or_else(|| panic!("missing CPU base cache poly for offset {off}"));
        assert_eq!(golden.len(), trace_len, "base cache {off} length");
        for row in 0..trace_len {
            assert_eq!(
                cache_base[pidx * trace_len + row],
                golden[row],
                "base cache offset {off} (poly_idx {pidx}) row {row}"
            );
        }
    }

    // inner gate outputs at InnerLayer{layer:1, offset}, read at `poly_idx`.
    for off in [
        1usize, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22,
    ] {
        let addr = GKRAddress::InnerLayer {
            layer: 1,
            offset: off,
        };
        let pidx = poly_idx_of(addr);
        let golden = gkr_storage.get_ext_poly(addr);
        assert_eq!(golden.len(), trace_len, "inner output {off} length");
        for row in 0..trace_len {
            assert_eq!(
                out_ext[pidx * trace_len + row],
                golden[row],
                "inner output offset {off} (poly_idx {pidx}) row {row}"
            );
        }
    }
}
