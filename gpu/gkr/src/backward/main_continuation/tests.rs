use std::cell::Cell;
use std::sync::OnceLock;

use gpu_gkr_compiler::{
    ImmediateId, MainContinuationWindowProgram, MainContinuationWindowShape, WindowFamily,
    MAIN_CONTINUATION_WINDOW_SHAPE_DEFINED_BITS,
};

const EXACT_MASKS: [u16; 7] = [0x00, 0x01, 0x03, 0x07, 0x13, 0x17, 0x1f];
const MIN_CASES_PER_MASK: usize = 32;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum InputPath {
    FirstRaw,
    LaterPrior,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct CaseSpec {
    mask_index: usize,
    case_index: usize,
    program_index: usize,
    suffix_bits: usize,
    input_path: InputPath,
}

fn case_specs() -> Vec<CaseSpec> {
    programs_by_mask()
        .iter()
        .enumerate()
        .flat_map(|(mask_index, programs)| {
            let case_count = MIN_CASES_PER_MASK.max(2 * programs.len());
            (0..case_count).map(move |case_index| CaseSpec {
                mask_index,
                case_index,
                program_index: (case_index / 2) % programs.len(),
                // Wide corpus programs stay tiny; one prior case per mask
                // crosses the 32-row tile boundary deterministically.
                suffix_bits: if case_index == 1 { 6 } else { 1 },
                input_path: if case_index.is_multiple_of(2) {
                    InputPath::FirstRaw
                } else {
                    InputPath::LaterPrior
                },
            })
        })
        .collect()
}

fn programs_by_mask() -> &'static Vec<Vec<MainContinuationWindowProgram>> {
    static PROGRAMS: OnceLock<Vec<Vec<MainContinuationWindowProgram>>> = OnceLock::new();
    PROGRAMS.get_or_init(|| {
        let mut by_mask = vec![Vec::new(); EXACT_MASKS.len()];
        for (layout, _) in crate::backward::CONTINUATION_GOLDEN_CORPUS {
            let (programs, _) = crate::backward::compile_corpus_layout(layout);
            let bundle = programs
                .resolve_main_continuation_window_programs()
                .expect("the retained continuation corpus lowers");
            for program in &bundle.layers {
                let index = EXACT_MASKS
                    .iter()
                    .position(|mask| *mask == program.shape.bits())
                    .expect("the retained corpus uses exactly the seven generated masks");
                by_mask[index].push(program.clone());
            }
        }
        for programs in &mut by_mask {
            programs.sort_by_key(|program| program.sources.len());
            assert!(
                !programs.is_empty(),
                "every exact mask needs a corpus fixture"
            );
        }
        by_mask
    })
}

#[test]
fn cpu_main_continuation_gpu_fixture_contract() {
    assert_eq!(
        EXACT_MASKS,
        [
            0x00,
            0x01,
            0x03,
            0x07,
            0x13,
            0x17,
            MAIN_CONTINUATION_WINDOW_SHAPE_DEFINED_BITS
        ]
    );

    let plans = case_specs();
    for mask_index in 0..EXACT_MASKS.len() {
        let mask_plans: Vec<_> = plans
            .iter()
            .filter(|plan| plan.mask_index == mask_index)
            .collect();
        let program_count = programs_by_mask()[mask_index].len();
        assert_eq!(mask_plans.len(), MIN_CASES_PER_MASK.max(2 * program_count));
        assert!(mask_plans.len() >= MIN_CASES_PER_MASK);
        assert!(mask_plans.iter().any(|plan| plan.suffix_bits == 1));
        assert!(mask_plans.iter().any(|plan| plan.suffix_bits == 6));
        assert!(mask_plans
            .iter()
            .any(|plan| plan.input_path == InputPath::FirstRaw));
        assert!(mask_plans
            .iter()
            .any(|plan| plan.input_path == InputPath::LaterPrior));
        for program_index in 0..program_count {
            assert!(mask_plans.iter().any(|plan| {
                plan.program_index == program_index && plan.input_path == InputPath::FirstRaw
            }));
            assert!(mask_plans.iter().any(|plan| {
                plan.program_index == program_index && plan.input_path == InputPath::LaterPrior
            }));
        }
    }

    let programs = programs_by_mask();
    assert_eq!(programs.iter().map(Vec::len).sum::<usize>(), 57);
    let mut raw_base = false;
    let mut raw_ext = false;
    let mut procedural = false;
    let mut selected_raw_base = false;
    let mut selected_raw_ext = false;
    let mut selected_procedural = false;
    let mut maximum_sources = 0usize;
    for (mask_index, bank) in programs.iter().enumerate() {
        assert!(bank.iter().all(|program| {
            program.shape
                == MainContinuationWindowShape::from_bits(EXACT_MASKS[mask_index]).unwrap()
        }));
        for program in bank {
            maximum_sources = maximum_sources.max(program.sources.len());
            for source in &program.sources {
                match source.raw_family {
                    WindowFamily::VirtualSetup { .. } => procedural = true,
                    WindowFamily::LayerOutput { ext: true, .. }
                    | WindowFamily::CacheOutput { ext: true, .. } => raw_ext = true,
                    _ => raw_base = true,
                }
            }
        }
    }
    assert!((raw_base, raw_ext, procedural) == (true, true, true));
    assert_eq!(maximum_sources, 1_012);
    let (blake2_programs, _) =
        crate::backward::compile_corpus_layout("blake2_with_extended_control_layout_gkr.json");
    assert_eq!(
        blake2_programs
            .resolve_main_continuation_window_programs()
            .unwrap()
            .layers[0]
            .sources
            .len(),
        1_012,
        "the maximum-source smoke is blake2_with_extended_control layer zero"
    );

    for plan in plans
        .iter()
        .filter(|plan| plan.input_path == InputPath::FirstRaw)
    {
        let bank = &programs[plan.mask_index];
        let program = &bank[plan.program_index];
        for source in &program.sources {
            match source.raw_family {
                WindowFamily::VirtualSetup { .. } => selected_procedural = true,
                WindowFamily::LayerOutput { ext: true, .. }
                | WindowFamily::CacheOutput { ext: true, .. } => selected_raw_ext = true,
                _ => selected_raw_base = true,
            }
        }
        if program.shape.contains(MainContinuationWindowShape::C_INIT) {
            assert!(program.c_init.is_some());
        }
        if program.shape.contains(MainContinuationWindowShape::GROUPED) {
            assert!(!program.grouped_records.is_empty());
        }
        if program
            .shape
            .contains(MainContinuationWindowShape::BANKED_GROUP_IMMEDIATE)
        {
            assert!(program.grouped_records.iter().any(|group| {
                group
                    .members
                    .iter()
                    .any(|member| ImmediateId(member.coeff).bank_index().is_some())
            }));
        }
        if program
            .shape
            .contains(MainContinuationWindowShape::NEGATIVE_GROUP_IMMEDIATE)
        {
            assert!(program.grouped_records.iter().any(|group| {
                group
                    .members
                    .iter()
                    .any(|member| ImmediateId(member.coeff) == ImmediateId::NEG_ONE)
            }));
        }
    }
    assert_eq!(
        (selected_raw_base, selected_raw_ext, selected_procedural),
        (true, true, true),
        "the executed first-window cases must exercise every raw source origin"
    );

    // The invalid shapes never become a dispatchable typed shape, so the
    // launch-side effect remains zero. The positive control makes this gate
    // mutation-sensitive rather than merely repeating `is_err`.
    let launch_constructions = Cell::new(0usize);
    let construct_launch = |bits| {
        let shape = MainContinuationWindowShape::from_bits(bits)?;
        launch_constructions.set(launch_constructions.get() + 1);
        Ok::<_, gpu_gkr_compiler::MainContinuationWindowLoweringError>(shape)
    };
    assert!(matches!(
        construct_launch(0x20),
        Err(
            gpu_gkr_compiler::MainContinuationWindowLoweringError::UndefinedShapeBits {
                bits: 0x20
            }
        )
    ));
    assert!(matches!(
        construct_launch(0x3f),
        Err(
            gpu_gkr_compiler::MainContinuationWindowLoweringError::UndefinedShapeBits {
                bits: 0x3f
            }
        )
    ));
    assert_eq!(launch_constructions.get(), 0);
    assert_eq!(construct_launch(0x1f).unwrap().bits(), 0x1f);
    assert_eq!(launch_constructions.get(), 1);
}

#[cfg(not(no_cuda))]
mod gpu {
    use std::collections::{BTreeMap, BTreeSet};
    use std::sync::{Arc, Mutex};

    use era_cudart::event::{CudaEvent, CudaEventCreateFlags};
    use era_cudart::memory::memory_copy_async;
    use era_cudart::slice::DeviceSlice;
    use gpu_core::allocator::tracker::AllocationPlacement;
    use gpu_core::primitives::callbacks::Callbacks;
    use gpu_core::primitives::context::{DeviceAllocation, HostAllocation};
    use gpu_core::primitives::field::{BF, E4};
    use gpu_core::primitives::static_host::{alloc_static_pinned_box_from_slice, StaticPinnedBox};
    use gpu_gkr_compiler::{
        CoefficientRecipeId, MainContinuationWindowProgram, MainContinuationWindowShape,
        WindowFamily,
    };
    use gpu_prover_context::ProverContext;

    use super::{
        case_specs, programs_by_mask, CaseSpec, InputPath, EXACT_MASKS, MIN_CASES_PER_MASK,
    };
    use crate::backward::kernels::{
        get_eq_high_constant_device_ptr, get_main_layer_claim_point_device_ptr,
        launch_build_eq_high_and_low_groups_from_point, resolve_active_eq_slot,
        GKR_EQ_GROUP_TABLE_LEN,
    };
    use crate::backward::main_continuation::abi::{
        MAIN_CONTINUATION_WINDOW_ROWS_PER_TILE, MAIN_CONTINUATION_WINDOW_TENSOR_CELLS,
    };
    use crate::backward::main_continuation::binding::{
        bind_first_main_continuation_window, bind_later_main_continuation_window,
        launch_main_continuation_window, MainContinuationWindowBindError,
        MainContinuationWindowRuntimeScratch,
    };
    use crate::backward::main_continuation::{
        continuation_window_tensor_reference, ContinuationPublishedLevel,
        ContinuationPublishedShape,
    };
    use crate::backward::make_eq_sizes;
    use crate::backward::vm::production_bind::family_read_place;
    use crate::backward::vm::seg::{
        bwd_seg_coeff_bank_device_ptr, launch_bwd_seg_build_fold_weights,
    };
    use crate::backward::vm::seg_desc::BWD_SEG_OUTPUT_BANK;
    use crate::backward::window::reference::tensor_round_tail_reference;
    use crate::backward::window::tail::{
        launch_window_tensor_round_tail, WindowTailArm, WindowTailState,
    };
    use crate::forward::vm::lower::read_place_to_gkr_address;
    use crate::test_utils::make_test_context;
    use crate::upstream::{Field, FieldExtension, PrimeField};
    use crate::{GpuBaseFieldPoly, GpuExtensionFieldPoly, GpuGKRStorage};

    #[derive(Clone, Copy, Debug)]
    struct Rng(u64);

    impl Rng {
        fn next_u32(&mut self) -> u32 {
            self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut value = self.0;
            value = (value ^ (value >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            value = (value ^ (value >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            (value ^ (value >> 31)) as u32
        }

        fn next_bf(&mut self) -> BF {
            BF::from_u32_with_reduction(self.next_u32())
        }

        fn next_e4(&mut self) -> E4 {
            E4::from_array_of_base(core::array::from_fn(|_| self.next_bf()))
        }
    }

    fn lift(value: BF) -> E4 {
        <E4 as FieldExtension<BF>>::from_base(value)
    }

    fn add(mut left: E4, right: E4) -> E4 {
        left.add_assign(&right);
        left
    }

    fn sub(mut left: E4, right: E4) -> E4 {
        left.sub_assign(&right);
        left
    }

    fn mul(mut left: E4, right: E4) -> E4 {
        left.mul_assign(&right);
        left
    }

    fn eq_weight(bit: usize, coordinate: E4) -> E4 {
        if bit == 0 {
            sub(E4::ONE, coordinate)
        } else {
            coordinate
        }
    }

    fn suffix_eq(point: &[E4]) -> Vec<E4> {
        (0..1usize << point.len())
            .map(|row| {
                point
                    .iter()
                    .enumerate()
                    .fold(E4::ONE, |weight, (bit, coordinate)| {
                        mul(weight, eq_weight((row >> bit) & 1, *coordinate))
                    })
            })
            .collect()
    }

    fn fold_eight(leaves: [E4; 8], coordinates: &[E4]) -> E4 {
        assert_eq!(coordinates.len(), 3);
        let leaf0 = leaves[0];
        (1..8).fold(leaf0, |value, q| {
            let weight = coordinates
                .iter()
                .enumerate()
                .fold(E4::ONE, |weight, (bit, coordinate)| {
                    mul(weight, eq_weight((q >> bit) & 1, *coordinate))
                });
            add(value, mul(weight, sub(leaves[q], leaf0)))
        })
    }

    fn virtual_value(kind: u8, index: usize) -> BF {
        match kind {
            0 if index < 1 << 16 => BF::from_u32_with_reduction(index as u32),
            1 if index < 1 << 19 => BF::from_u32_with_reduction(index as u32),
            0 | 1 => BF::ZERO,
            2 => BF::from_u32_with_reduction(((index << 2) & 0xffff) as u32),
            3 => BF::from_u32_with_reduction((index >> 14) as u32),
            _ => panic!("undefined procedural source kind {kind}"),
        }
    }

    fn raw_is_ext(family: WindowFamily) -> bool {
        matches!(
            family,
            WindowFamily::LayerOutput { ext: true, .. }
                | WindowFamily::CacheOutput { ext: true, .. }
        )
    }

    fn upload<T: Copy>(
        context: &ProverContext,
        host: &[T],
    ) -> (DeviceAllocation<T>, StaticPinnedBox<T>) {
        let staging = alloc_static_pinned_box_from_slice(host).unwrap();
        let mut device = context
            .alloc(host.len().max(1), AllocationPlacement::BestFit)
            .unwrap();
        memory_copy_async(
            &mut device[..host.len()],
            &staging[..],
            context.get_exec_stream(),
        )
        .unwrap();
        (device, staging)
    }

    fn write_symbol(context: &ProverContext, pointer: *mut E4, host: &[E4]) -> StaticPinnedBox<E4> {
        let staging = alloc_static_pinned_box_from_slice(host).unwrap();
        // SAFETY: callers size the source to the matching static symbol.
        let device = unsafe { DeviceSlice::from_raw_parts_mut(pointer, host.len()) };
        memory_copy_async(device, &staging[..], context.get_exec_stream()).unwrap();
        staging
    }

    struct RawInput {
        storage: GpuGKRStorage<BF, E4>,
        _base_host: Vec<BF>,
        _ext_host: Vec<E4>,
        _base_staging: Option<StaticPinnedBox<BF>>,
        _ext_staging: Option<StaticPinnedBox<E4>>,
    }

    struct PriorInput {
        published: ContinuationPublishedLevel,
        _host: Vec<E4>,
        _staging: StaticPinnedBox<E4>,
    }

    enum InputOwner {
        Raw(RawInput),
        Prior(PriorInput),
    }

    struct PreparedCase {
        start_round: usize,
        folding_steps: usize,
        claim_point: Vec<E4>,
        source_rows: Vec<Vec<[E4; 8]>>,
        coefficient_bank: Vec<E4>,
        eq_suffix: Vec<E4>,
        seed: [u32; 8],
        claim: E4,
        eq_prefactor: E4,
        input: InputOwner,
    }

    fn build_raw_input(
        program: &MainContinuationWindowProgram,
        trace_len: usize,
        logical_rows: usize,
        fold_coordinates: &[E4],
        rng: &mut Rng,
        context: &ProverContext,
    ) -> (RawInput, Vec<Vec<[E4; 8]>>) {
        let mut base_addresses = BTreeSet::new();
        let mut ext_addresses = BTreeSet::new();
        for source in &program.sources {
            if let Some(place) = family_read_place(source.raw_family, source.raw_column) {
                let address = read_place_to_gkr_address(&place);
                if raw_is_ext(source.raw_family) {
                    ext_addresses.insert(address);
                } else {
                    base_addresses.insert(address);
                }
            }
        }
        let base_rank: BTreeMap<_, _> = base_addresses
            .iter()
            .copied()
            .enumerate()
            .map(|(rank, address)| (address, rank))
            .collect();
        let ext_rank: BTreeMap<_, _> = ext_addresses
            .iter()
            .copied()
            .enumerate()
            .map(|(rank, address)| (address, rank))
            .collect();

        let mut base_host = vec![BF::ZERO; base_rank.len() * trace_len];
        for rank in 0..base_rank.len() {
            for group in 0..trace_len / 8 {
                let value = rng.next_bf();
                base_host[rank * trace_len + 8 * group..rank * trace_len + 8 * group + 8]
                    .fill(value);
            }
        }
        let mut ext_host = vec![E4::ZERO; ext_rank.len() * trace_len];
        for rank in 0..ext_rank.len() {
            for group in 0..trace_len / 8 {
                let value = rng.next_e4();
                ext_host[rank * trace_len + 8 * group..rank * trace_len + 8 * group + 8]
                    .fill(value);
            }
        }

        let source_rows = program
            .sources
            .iter()
            .map(|source| {
                (0..logical_rows)
                    .map(|row| {
                        core::array::from_fn(|corner| {
                            let group = 8 * row + corner;
                            match source.raw_family {
                                WindowFamily::VirtualSetup { kind } => {
                                    let leaves = core::array::from_fn(|q| {
                                        lift(virtual_value(kind, 8 * group + q))
                                    });
                                    fold_eight(leaves, fold_coordinates)
                                }
                                family if raw_is_ext(family) => {
                                    let place =
                                        family_read_place(family, source.raw_column).unwrap();
                                    let rank = ext_rank[&read_place_to_gkr_address(&place)];
                                    ext_host[rank * trace_len + 8 * group]
                                }
                                family => {
                                    let place =
                                        family_read_place(family, source.raw_column).unwrap();
                                    let rank = base_rank[&read_place_to_gkr_address(&place)];
                                    lift(base_host[rank * trace_len + 8 * group])
                                }
                            }
                        })
                    })
                    .collect()
            })
            .collect();

        let mut storage = GpuGKRStorage::default();
        let mut base_staging = None;
        if !base_host.is_empty() {
            let (device, staging) = upload(context, &base_host);
            let backing = Arc::new(device);
            base_staging = Some(staging);
            for (address, rank) in &base_rank {
                let layer = GpuGKRStorage::<BF, E4>::base_poly_layer(*address).unwrap();
                storage.insert_base_field_at_layer(
                    layer,
                    *address,
                    GpuBaseFieldPoly::from_arc(Arc::clone(&backing), rank * trace_len, trace_len),
                );
            }
        }
        let mut ext_staging = None;
        if !ext_host.is_empty() {
            let (device, staging) = upload(context, &ext_host);
            let backing = Arc::new(device);
            ext_staging = Some(staging);
            for (address, rank) in &ext_rank {
                let layer = GpuGKRStorage::<BF, E4>::ext_poly_layer(*address).unwrap();
                storage.insert_extension_at_layer(
                    layer,
                    *address,
                    GpuExtensionFieldPoly::from_arc(
                        Arc::clone(&backing),
                        rank * trace_len,
                        trace_len,
                    ),
                );
            }
        }
        (
            RawInput {
                storage,
                _base_host: base_host,
                _ext_host: ext_host,
                _base_staging: base_staging,
                _ext_staging: ext_staging,
            },
            source_rows,
        )
    }

    fn build_prior_input(
        program: &MainContinuationWindowProgram,
        logical_rows: usize,
        rng: &mut Rng,
        context: &ProverContext,
    ) -> (PriorInput, Vec<Vec<[E4; 8]>>) {
        let column_elems = logical_rows * 64;
        let mut host = vec![E4::ZERO; program.sources.len() * column_elems];
        let mut source_rows = vec![vec![[E4::ZERO; 8]; logical_rows]; program.sources.len()];
        for source in 0..program.sources.len() {
            for row in 0..logical_rows {
                for corner in 0..8 {
                    let value = rng.next_e4();
                    source_rows[source][row][corner] = value;
                    let begin = source * column_elems + 64 * row + 8 * corner;
                    host[begin..begin + 8].fill(value);
                }
            }
        }
        let (allocation, staging) = upload(context, &host);
        let shape = ContinuationPublishedShape {
            depth: 3,
            columns: program.sources.len(),
            column_elems,
        };
        let published = ContinuationPublishedLevel::try_new(
            shape,
            allocation,
            program
                .sources
                .iter()
                .map(|source| (source.id, usize::from(source.publish_column))),
        )
        .unwrap();
        (
            PriorInput {
                published,
                _host: host,
                _staging: staging,
            },
            source_rows,
        )
    }

    fn prepare_case(
        spec: CaseSpec,
        program: &MainContinuationWindowProgram,
        context: &ProverContext,
    ) -> PreparedCase {
        let start_round = match spec.input_path {
            InputPath::FirstRaw => 3,
            InputPath::LaterPrior => 6,
        };
        let folding_steps = start_round + 3 + spec.suffix_bits;
        let logical_rows = 1usize << spec.suffix_bits;
        let mut rng = Rng(0xc017_1a77_0000_0000
            ^ ((spec.mask_index as u64) << 40)
            ^ ((spec.case_index as u64) << 16));
        let claim_point: Vec<E4> = (0..folding_steps + 1).map(|_| rng.next_e4()).collect();
        let fold_coordinates = &claim_point[start_round - 3..start_round];
        let (input, source_rows) = match spec.input_path {
            InputPath::FirstRaw => {
                let trace_len = 1usize << folding_steps;
                let (raw, source_rows) = build_raw_input(
                    program,
                    trace_len,
                    logical_rows,
                    fold_coordinates,
                    &mut rng,
                    context,
                );
                (InputOwner::Raw(raw), source_rows)
            }
            InputPath::LaterPrior => {
                let (prior, source_rows) =
                    build_prior_input(program, logical_rows, &mut rng, context);
                (InputOwner::Prior(prior), source_rows)
            }
        };
        let mut coefficient_bank = (0..BWD_SEG_OUTPUT_BANK)
            .map(|_| rng.next_e4())
            .collect::<Vec<_>>();
        coefficient_bank[CoefficientRecipeId::ONE.0 as usize] = E4::ONE;
        coefficient_bank[CoefficientRecipeId::NEG_ONE.0 as usize] = sub(E4::ZERO, E4::ONE);
        let eq_suffix = suffix_eq(&claim_point[start_round + 3..folding_steps]);
        PreparedCase {
            start_round,
            folding_steps,
            claim_point,
            source_rows,
            coefficient_bank,
            eq_suffix,
            seed: core::array::from_fn(|_| rng.next_u32()),
            claim: rng.next_e4(),
            eq_prefactor: rng.next_e4(),
            input,
        }
    }

    #[derive(Debug, Default)]
    struct Observation {
        publication: Vec<E4>,
        partials: Vec<E4>,
        reduced_tensor: Vec<E4>,
        coefficients: Vec<E4>,
        challenges: Vec<E4>,
        seed: Vec<u32>,
        claim: Vec<E4>,
        eq_prefactor: Vec<E4>,
        eq_before: Vec<E4>,
        eq_after: Vec<E4>,
        active_eq_size_before_fold: u32,
    }

    struct ReadbackJob {
        finished: CudaEvent,
        callbacks: Callbacks<'static>,
        _publication_host: HostAllocation<[E4]>,
        _partials_host: HostAllocation<[E4]>,
        _tensor_host: Option<HostAllocation<[E4]>>,
        _coefficients_host: HostAllocation<[E4]>,
        _challenges_host: HostAllocation<[E4]>,
        _seed_host: HostAllocation<[u32]>,
        _claim_host: HostAllocation<[E4]>,
        _prefactor_host: HostAllocation<[E4]>,
        _eq_before_host: HostAllocation<[E4]>,
        _eq_after_host: HostAllocation<[E4]>,
        output: Arc<Mutex<Option<Observation>>>,
    }

    impl ReadbackJob {
        fn finish(self) -> Observation {
            self.finished.synchronize().unwrap();
            drop(self.callbacks);
            let output = Arc::try_unwrap(self.output)
                .ok()
                .expect("the readback callback releases its result handle");
            output
                .into_inner()
                .unwrap()
                .expect("the recorded completion event follows the readback callback")
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn schedule_readback(
        publication: &DeviceAllocation<E4>,
        partials: &DeviceSlice<E4>,
        reduced_tensor: Option<&DeviceSlice<E4>>,
        coefficients: &DeviceAllocation<E4>,
        challenges: &DeviceAllocation<E4>,
        seed: &DeviceAllocation<u32>,
        claim: &DeviceAllocation<E4>,
        eq_prefactor: &DeviceAllocation<E4>,
        eq_before_host: HostAllocation<[E4]>,
        active_eq: &DeviceSlice<E4>,
        active_eq_size_before_fold: u32,
        context: &ProverContext,
    ) -> ReadbackJob {
        let stream = context.get_exec_stream();
        let mut publication_host = unsafe { context.alloc_host_uninit_slice(publication.len()) };
        let mut partials_host = unsafe { context.alloc_host_uninit_slice(partials.len()) };
        let mut tensor_host = reduced_tensor
            .map(|tensor| unsafe { context.alloc_host_uninit_slice::<E4>(tensor.len()) });
        let mut coefficients_host = unsafe { context.alloc_host_uninit_slice(coefficients.len()) };
        let mut challenges_host = unsafe { context.alloc_host_uninit_slice(challenges.len()) };
        let mut seed_host = unsafe { context.alloc_host_uninit_slice(seed.len()) };
        let mut claim_host = unsafe { context.alloc_host_uninit_slice(claim.len()) };
        let mut prefactor_host = unsafe { context.alloc_host_uninit_slice(eq_prefactor.len()) };
        let mut eq_after_host = unsafe { context.alloc_host_uninit_slice(active_eq.len()) };
        memory_copy_async(&mut publication_host, publication, stream).unwrap();
        memory_copy_async(&mut partials_host, partials, stream).unwrap();
        if let (Some(tensor_host), Some(reduced_tensor)) = (tensor_host.as_mut(), reduced_tensor) {
            memory_copy_async(tensor_host, reduced_tensor, stream).unwrap();
        }
        memory_copy_async(&mut coefficients_host, coefficients, stream).unwrap();
        memory_copy_async(&mut challenges_host, challenges, stream).unwrap();
        memory_copy_async(&mut seed_host, seed, stream).unwrap();
        memory_copy_async(&mut claim_host, claim, stream).unwrap();
        memory_copy_async(&mut prefactor_host, eq_prefactor, stream).unwrap();
        memory_copy_async(&mut eq_after_host, active_eq, stream).unwrap();

        let publication_accessor = publication_host.get_accessor();
        let partials_accessor = partials_host.get_accessor();
        let tensor_accessor = tensor_host.as_ref().map(|host| host.get_accessor());
        let coefficients_accessor = coefficients_host.get_accessor();
        let challenges_accessor = challenges_host.get_accessor();
        let seed_accessor = seed_host.get_accessor();
        let claim_accessor = claim_host.get_accessor();
        let prefactor_accessor = prefactor_host.get_accessor();
        let eq_before_accessor = eq_before_host.get_accessor();
        let eq_after_accessor = eq_after_host.get_accessor();
        let output = Arc::new(Mutex::new(None));
        let callback_output = Arc::clone(&output);
        let mut callbacks = Callbacks::new();
        callbacks
            .schedule(
                move || unsafe {
                    callback_output.lock().unwrap().replace(Observation {
                        publication: publication_accessor.get().to_vec(),
                        partials: partials_accessor.get().to_vec(),
                        reduced_tensor: tensor_accessor
                            .map_or_else(Vec::new, |accessor| accessor.get().to_vec()),
                        coefficients: coefficients_accessor.get().to_vec(),
                        challenges: challenges_accessor.get().to_vec(),
                        seed: seed_accessor.get().to_vec(),
                        claim: claim_accessor.get().to_vec(),
                        eq_prefactor: prefactor_accessor.get().to_vec(),
                        eq_before: eq_before_accessor.get().to_vec(),
                        eq_after: eq_after_accessor.get().to_vec(),
                        active_eq_size_before_fold,
                    });
                },
                stream,
            )
            .unwrap();
        let finished = CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING).unwrap();
        finished.record(stream).unwrap();
        ReadbackJob {
            finished,
            callbacks,
            _publication_host: publication_host,
            _partials_host: partials_host,
            _tensor_host: tensor_host,
            _coefficients_host: coefficients_host,
            _challenges_host: challenges_host,
            _seed_host: seed_host,
            _claim_host: claim_host,
            _prefactor_host: prefactor_host,
            _eq_before_host: eq_before_host,
            _eq_after_host: eq_after_host,
            output,
        }
    }

    fn reduce_partials(partials: &[E4], row_tiles: usize) -> [E4; 27] {
        assert_eq!(
            partials.len(),
            row_tiles * MAIN_CONTINUATION_WINDOW_TENSOR_CELLS
        );
        core::array::from_fn(|cell| {
            (0..row_tiles).fold(E4::ZERO, |sum, tile| {
                add(
                    sum,
                    partials[tile * MAIN_CONTINUATION_WINDOW_TENSOR_CELLS + cell],
                )
            })
        })
    }

    fn expected_publication(source_rows: &[Vec<[E4; 8]>]) -> Vec<E4> {
        source_rows
            .iter()
            .flat_map(|rows| rows.iter().flat_map(|corners| corners.iter().copied()))
            .collect()
    }

    fn run_arm(
        program: &MainContinuationWindowProgram,
        prepared: &PreparedCase,
        arm: WindowTailArm,
        context: &ProverContext,
    ) -> Observation {
        let _coefficient_staging = write_symbol(
            context,
            bwd_seg_coeff_bank_device_ptr(),
            &prepared.coefficient_bank,
        );
        let _claim_symbol_staging = write_symbol(
            context,
            get_main_layer_claim_point_device_ptr(),
            &prepared.claim_point,
        );
        let (claim_point, _claim_point_staging) = upload(context, &prepared.claim_point);
        let mut eq_low = context
            .alloc(GKR_EQ_GROUP_TABLE_LEN, AllocationPlacement::BestFit)
            .unwrap();
        launch_build_eq_high_and_low_groups_from_point(
            claim_point.as_ptr(),
            prepared.start_round + 3,
            prepared.folding_steps - prepared.start_round - 3,
            get_eq_high_constant_device_ptr(),
            eq_low.as_mut_ptr(),
            context,
        )
        .unwrap();
        launch_bwd_seg_build_fold_weights(prepared.start_round as u32, context).unwrap();

        let logical_rows = 1usize << (prepared.folding_steps - prepared.start_round - 3);
        let row_tiles = logical_rows.div_ceil(MAIN_CONTINUATION_WINDOW_ROWS_PER_TILE);
        let mut partials = context
            .alloc(
                MAIN_CONTINUATION_WINDOW_TENSOR_CELLS * (row_tiles + 1),
                AllocationPlacement::BestFit,
            )
            .unwrap();
        let scratch = MainContinuationWindowRuntimeScratch {
            eq_low: eq_low.as_ptr(),
            partials: partials.as_mut_ptr(),
            partials_capacity: partials.len(),
        };
        let launch = match &prepared.input {
            InputOwner::Raw(raw) => bind_first_main_continuation_window(
                program,
                &raw.storage,
                prepared.folding_steps,
                prepared.start_round,
                scratch,
                context,
            ),
            InputOwner::Prior(prior) => bind_later_main_continuation_window(
                program,
                &prior.published,
                prepared.folding_steps,
                prepared.start_round,
                scratch,
                context,
            ),
        }
        .unwrap();
        let launched = launch_main_continuation_window(launch, context).unwrap();
        assert_eq!(launched.row_tiles(), row_tiles);
        assert_eq!(
            launched.eq_sizes(),
            make_eq_sizes(prepared.folding_steps - prepared.start_round - 3)
        );
        assert_eq!(
            launched.published_level().shape(),
            ContinuationPublishedShape {
                depth: prepared.start_round as u8,
                columns: program.sources.len(),
                column_elems: 8 * logical_rows,
            }
        );

        let (mut seed, _seed_staging) = upload(context, &prepared.seed);
        let (mut claim, _claim_staging) = upload(context, &[prepared.claim]);
        let (mut eq_prefactor, _prefactor_staging) = upload(context, &[prepared.eq_prefactor]);
        let mut coefficients = context.alloc(12, AllocationPlacement::BestFit).unwrap();
        let mut challenges = context.alloc(3, AllocationPlacement::BestFit).unwrap();
        let eq_sizes = launched.eq_sizes();
        let (active_eq_slot_base, active_eq_size_before_fold) =
            resolve_active_eq_slot(&eq_sizes, eq_low.as_mut_ptr());
        let active_eq = unsafe {
            DeviceSlice::from_raw_parts(active_eq_slot_base as *const E4, GKR_EQ_GROUP_TABLE_LEN)
        };
        let mut eq_before_host =
            unsafe { context.alloc_host_uninit_slice::<E4>(GKR_EQ_GROUP_TABLE_LEN) };
        memory_copy_async(&mut eq_before_host, active_eq, context.get_exec_stream()).unwrap();
        let tail = WindowTailState {
            partials: partials.as_ptr(),
            row_tiles: launched.row_tiles(),
            reduced_tensor: launched.reduced_tensor(),
            prev_claim_coords: unsafe { claim_point.as_ptr().add(prepared.start_round) },
            seed: seed.as_mut_ptr(),
            claim: claim.as_mut_ptr(),
            eq_prefactor: eq_prefactor.as_mut_ptr(),
            coeffs_out: coefficients.as_mut_ptr(),
            challenges_out: challenges.as_mut_ptr(),
            active_eq_slot_base,
            active_eq_size_before_fold,
        };
        launch_window_tensor_round_tail(arm, &tail, context).unwrap();

        let reduced = unsafe {
            DeviceSlice::from_raw_parts(
                launched.reduced_tensor() as *const E4,
                MAIN_CONTINUATION_WINDOW_TENSOR_CELLS,
            )
        };
        schedule_readback(
            launched.published_level().allocation(),
            &partials[..MAIN_CONTINUATION_WINDOW_TENSOR_CELLS * row_tiles],
            (arm == WindowTailArm::Split).then_some(reduced),
            &coefficients,
            &challenges,
            &seed,
            &claim,
            &eq_prefactor,
            eq_before_host,
            active_eq,
            active_eq_size_before_fold,
            context,
        )
        .finish()
    }

    #[allow(clippy::too_many_arguments)]
    fn assert_arm(
        label: &str,
        observation: &Observation,
        expected_tensor: [E4; 27],
        expected_publication: &[E4],
        expected_coefficients: [E4; 12],
        expected_challenges: [E4; 3],
        expected_seed: [u32; 8],
        expected_claim: E4,
        expected_eq_prefactor: E4,
        expect_reduced_tensor: bool,
    ) {
        assert_eq!(
            observation.publication, expected_publication,
            "{label} publication"
        );
        let row_tiles = observation.partials.len() / MAIN_CONTINUATION_WINDOW_TENSOR_CELLS;
        assert_eq!(
            reduce_partials(&observation.partials, row_tiles),
            expected_tensor,
            "{label} tensor"
        );
        if expect_reduced_tensor {
            assert_eq!(
                observation.reduced_tensor, expected_tensor,
                "{label} reduced tensor"
            );
        }
        assert_eq!(
            observation.coefficients, expected_coefficients,
            "{label} coefficients"
        );
        assert_eq!(
            observation.challenges, expected_challenges,
            "{label} challenges"
        );
        assert_eq!(observation.seed, expected_seed, "{label} seed");
        assert_eq!(observation.claim, [expected_claim], "{label} claim");
        assert_eq!(
            observation.eq_prefactor,
            [expected_eq_prefactor],
            "{label} eq prefactor"
        );
        assert_eq!(observation.eq_before.len(), GKR_EQ_GROUP_TABLE_LEN);
        assert_eq!(observation.eq_after.len(), GKR_EQ_GROUP_TABLE_LEN);
        let folded_len = 1usize << (observation.active_eq_size_before_fold - 1);
        for index in 0..GKR_EQ_GROUP_TABLE_LEN {
            let expected = if index < folded_len {
                add(
                    observation.eq_before[2 * index],
                    observation.eq_before[2 * index + 1],
                )
            } else {
                observation.eq_before[index]
            };
            assert_eq!(observation.eq_after[index], expected, "{label} eq[{index}]");
        }
    }

    fn exact_fallback_byte_gate(context: &ProverContext) {
        let mask_index = EXACT_MASKS.iter().position(|mask| *mask == 0x03).unwrap();
        let program = &programs_by_mask()[mask_index][0];
        let spec = CaseSpec {
            mask_index,
            case_index: 0,
            program_index: 0,
            suffix_bits: 1,
            input_path: InputPath::FirstRaw,
        };
        let prepared = prepare_case(spec, program, context);
        let exact = run_arm(program, &prepared, WindowTailArm::Split, context);
        let mut universal = program.clone();
        universal.shape = MainContinuationWindowShape::UNIVERSAL;
        let fallback = run_arm(&universal, &prepared, WindowTailArm::Split, context);
        assert_eq!(
            as_bytes(&exact.publication),
            as_bytes(&fallback.publication)
        );
        assert_eq!(as_bytes(&exact.partials), as_bytes(&fallback.partials));
        undefined_shape_runtime_gate(program, &prepared, context);
    }

    fn undefined_shape_runtime_gate(
        program: &MainContinuationWindowProgram,
        prepared: &PreparedCase,
        context: &ProverContext,
    ) {
        let raw = match &prepared.input {
            InputOwner::Raw(raw) => raw,
            InputOwner::Prior(_) => unreachable!(),
        };
        let mut invalid = program.clone();
        // SAFETY: the shape is repr(transparent); this deliberately bypasses
        // the compiler constructor to exercise the runtime prelaunch guard.
        invalid.shape = unsafe { std::mem::transmute::<u16, MainContinuationWindowShape>(0x20) };
        let eq_low: DeviceAllocation<E4> = context
            .alloc(GKR_EQ_GROUP_TABLE_LEN, AllocationPlacement::BestFit)
            .unwrap();
        let mut partials = context
            .alloc(
                2 * MAIN_CONTINUATION_WINDOW_TENSOR_CELLS,
                AllocationPlacement::BestFit,
            )
            .unwrap();
        let result = bind_first_main_continuation_window(
            &invalid,
            &raw.storage,
            prepared.folding_steps,
            prepared.start_round,
            MainContinuationWindowRuntimeScratch {
                eq_low: eq_low.as_ptr(),
                partials: partials.as_mut_ptr(),
                partials_capacity: partials.len(),
            },
            context,
        );
        assert!(matches!(
            result,
            Err(MainContinuationWindowBindError::UndefinedShapeBits { bits: 0x20 })
        ));
    }

    fn as_bytes<T: Copy>(values: &[T]) -> &[u8] {
        // SAFETY: the byte view has exactly the initialized slice's extent.
        unsafe {
            core::slice::from_raw_parts(values.as_ptr().cast::<u8>(), std::mem::size_of_val(values))
        }
    }

    #[test]
    fn main_continuation_window_gpu_oracle() {
        let context = make_test_context(1_024, 128);
        let mut per_mask = [0usize; EXACT_MASKS.len()];
        let mut coordinate_paths = BTreeSet::new();
        let expected_raw_families: BTreeSet<_> = programs_by_mask()
            .iter()
            .flat_map(|bank| bank.iter())
            .flat_map(|program| program.sources.iter().map(|source| source.raw_family))
            .collect();
        let mut observed_raw_families = BTreeSet::new();
        let mut prior_origin = false;
        let mut saw_c_init = false;
        let mut saw_grouped = false;
        let mut saw_banked = false;
        let mut saw_negative = false;
        let mut maximum_raw = false;
        let mut maximum_prior = false;
        for spec in case_specs() {
            let programs = &programs_by_mask()[spec.mask_index];
            let program = &programs[spec.program_index];
            assert_eq!(program.shape.bits(), EXACT_MASKS[spec.mask_index]);
            per_mask[spec.mask_index] += 1;
            coordinate_paths.insert((spec.mask_index, spec.program_index, spec.input_path));
            match spec.input_path {
                InputPath::FirstRaw => {
                    observed_raw_families
                        .extend(program.sources.iter().map(|source| source.raw_family));
                }
                InputPath::LaterPrior => prior_origin = true,
            }
            saw_c_init |= program.c_init.is_some();
            saw_grouped |= !program.grouped_records.is_empty();
            saw_banked |= program
                .shape
                .contains(MainContinuationWindowShape::BANKED_GROUP_IMMEDIATE);
            saw_negative |= program
                .shape
                .contains(MainContinuationWindowShape::NEGATIVE_GROUP_IMMEDIATE);
            let prepared = prepare_case(spec, program, &context);
            let expected_tensor = continuation_window_tensor_reference(
                program,
                &prepared.source_rows,
                &prepared.coefficient_bank,
                &prepared.eq_suffix,
            )
            .unwrap();
            let expected_publication = expected_publication(&prepared.source_rows);
            let rho: [E4; 3] =
                core::array::from_fn(|axis| prepared.claim_point[prepared.start_round + axis]);
            let mut expected_seed = prepared.seed;
            let mut expected_claim = prepared.claim;
            let mut expected_prefactor = prepared.eq_prefactor;
            let (expected_coefficients, expected_challenges) = tensor_round_tail_reference(
                expected_tensor,
                &rho,
                &mut expected_seed,
                &mut expected_claim,
                &mut expected_prefactor,
            );
            let absorbed = run_arm(program, &prepared, WindowTailArm::Absorbed, &context);
            let split = run_arm(program, &prepared, WindowTailArm::Split, &context);
            for (arm, observation) in [
                (WindowTailArm::Absorbed, &absorbed),
                (WindowTailArm::Split, &split),
            ] {
                let label = format!(
                    "mask {:02x} case {} {:?} {arm:?}",
                    program.shape.bits(),
                    spec.case_index,
                    spec.input_path
                );
                assert_arm(
                    &label,
                    &observation,
                    expected_tensor,
                    &expected_publication,
                    expected_coefficients,
                    expected_challenges,
                    expected_seed,
                    expected_claim,
                    expected_prefactor,
                    arm == WindowTailArm::Split,
                );
            }
            assert_eq!(
                as_bytes(&absorbed.publication),
                as_bytes(&split.publication)
            );
            assert_eq!(as_bytes(&absorbed.partials), as_bytes(&split.partials));
            assert_eq!(absorbed.coefficients, split.coefficients);
            assert_eq!(absorbed.challenges, split.challenges);
            assert_eq!(absorbed.seed, split.seed);
            assert_eq!(absorbed.claim, split.claim);
            assert_eq!(absorbed.eq_prefactor, split.eq_prefactor);
            assert_eq!(absorbed.eq_before, split.eq_before);
            assert_eq!(absorbed.eq_after, split.eq_after);

            if program.sources.len() == 1_012 {
                assert_eq!(spec.suffix_bits, 1);
                assert_eq!(
                    absorbed.partials.len(),
                    MAIN_CONTINUATION_WINDOW_TENSOR_CELLS
                );
                assert_eq!(absorbed.publication.len(), 1_012 * 16);
                match spec.input_path {
                    InputPath::FirstRaw => maximum_raw = true,
                    InputPath::LaterPrior => maximum_prior = true,
                }
            }
        }
        for (mask_index, programs) in programs_by_mask().iter().enumerate() {
            assert_eq!(
                per_mask[mask_index],
                MIN_CASES_PER_MASK.max(2 * programs.len())
            );
            for program_index in 0..programs.len() {
                assert!(coordinate_paths.contains(&(
                    mask_index,
                    program_index,
                    InputPath::FirstRaw
                )));
                assert!(coordinate_paths.contains(&(
                    mask_index,
                    program_index,
                    InputPath::LaterPrior
                )));
            }
        }
        assert_eq!(coordinate_paths.len(), 2 * 57);
        assert_eq!(observed_raw_families, expected_raw_families);
        assert!(prior_origin);
        assert!((saw_c_init, saw_grouped, saw_banked, saw_negative) == (true, true, true, true));
        assert!((maximum_raw, maximum_prior) == (true, true));
        exact_fallback_byte_gate(&context);
    }
}
