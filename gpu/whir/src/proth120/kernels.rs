use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;
use era_cudart::stream::CudaStream;
use era_cudart::{
    cuda_kernel, cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function,
};
use gpu_core::primitives::device_structures::DeviceMatrixChunkImpl;
use gpu_core::primitives::field::PR;
use gpu_hash::keccak256::Digest;
use gpu_ntt::proth120::TwiddleDescriptor;

const BLOCK: usize = 256;

#[repr(C)]
#[derive(Clone, Copy)]
struct BaseColumnsMetadata {
    values: [*const PR; 2],
    columns: [u32; 2],
    strides: [u64; 2],
    powers: *const PR,
    result: *mut PR,
    log_rows: u32,
    pack_log2: u32,
}

const _: () = {
    assert!(size_of::<PR>() == 16 && align_of::<PR>() == 16);
    assert!(size_of::<BaseColumnsMetadata>() == 64 && align_of::<BaseColumnsMetadata>() == 8);
    assert!(std::mem::offset_of!(BaseColumnsMetadata, values) == 0);
    assert!(std::mem::offset_of!(BaseColumnsMetadata, columns) == 16);
    assert!(std::mem::offset_of!(BaseColumnsMetadata, strides) == 24);
    assert!(std::mem::offset_of!(BaseColumnsMetadata, powers) == 40);
    assert!(std::mem::offset_of!(BaseColumnsMetadata, result) == 48);
    assert!(std::mem::offset_of!(BaseColumnsMetadata, log_rows) == 56);
    assert!(std::mem::offset_of!(BaseColumnsMetadata, pack_log2) == 60);
};

cuda_kernel!(AccumulateBase, ab_pr_whir_accumulate_base_columns_kernel(m: BaseColumnsMetadata));
cuda_kernel!(EqSplit, ab_pr_whir_eq_split_tables_kernel(point: *const PR, log_n: u32, low_bits: u32, lo: *mut PR, hi: *mut PR));
cuda_kernel!(EqJoin, ab_pr_whir_eq_from_split_tables_kernel(lo: *const PR, hi: *const PR, low_bits: u32, log_n: u32, eq: *mut PR));
cuda_kernel!(BatchedOpening, ab_pr_whir_batched_opening_kernel(powers: *const PR, claims: *const PR, count: u32, out: *mut PR));
cuda_kernel!(FoldAdjacent, ab_pr_whir_fold_adjacent_kernel(src: *const PR, dst: *mut PR, challenge: *const PR, half_len: u32));
cuda_kernel!(FoldAdjacentPair, ab_pr_whir_fold_adjacent_pair_kernel(src_a: *const PR, dst_a: *mut PR, src_b: *const PR, dst_b: *mut PR, challenge: *const PR, half_len: u32));
cuda_kernel!(ThreePointPartials, ab_pr_whir_three_point_partials_kernel(eval: *const PR, eq: *const PR, partials: *mut PR, half: u32));
cuda_kernel!(ThreePointFinalize, ab_pr_whir_three_point_finalize_kernel(partials: *const PR, num_blocks: u32, reduce_out: *mut PR));
cuda_kernel!(ThreePointCombined, ab_pr_whir_three_point_combined_kernel(eval: *const PR, eq: *const PR, reduce_out: *mut PR, half: u32));
cuda_kernel!(Sum, ab_pr_whir_sum_kernel(values: *const PR, count: u32, out: *mut PR));
cuda_kernel!(MonomialEval, ab_pr_whir_partially_evaluate_monomials_kernel(src: *const PR, dst: *mut PR, z: *const PR, z_stride: *const PR, log_count: u32));
cuda_kernel!(MonomialEvalSmall, ab_pr_whir_partially_evaluate_monomials_small_kernel(src: *const PR, dst: *mut PR, z: *const PR, log_count: u32));
cuda_kernel!(RoundUpdate, ab_pr_whir_fold_round_update_kernel(reductions: *mut PR, seed_io: *mut u8, coeffs_out: *mut PR, challenge_out: *mut PR));
cuda_kernel!(PlaceRoots, ab_pr_whir_place_roots_kernel(retained: *const Digest, retained_stride: u64, log_lde: u32, roots: *mut Digest));

cuda_kernel_signature_arguments_and_function!(
    ConvertTileLeaves,
    tile: *mut PR,
    log_n: u32,
    descriptor: TwiddleDescriptor,
    log_domain: u32,
    k0: u32,
    cosets: u32,
);

macro_rules! convert_tile_leaves_kernel {
    ($name:ident) => {
        cuda_kernel_declaration!($name(
            tile: *mut PR,
            log_n: u32,
            descriptor: TwiddleDescriptor,
            log_domain: u32,
            k0: u32,
            cosets: u32,
        ));
    };
}
convert_tile_leaves_kernel!(ab_pr_whir_convert_tile_leaves_1_kernel);
convert_tile_leaves_kernel!(ab_pr_whir_convert_tile_leaves_2_kernel);
convert_tile_leaves_kernel!(ab_pr_whir_convert_tile_leaves_3_kernel);
convert_tile_leaves_kernel!(ab_pr_whir_convert_tile_leaves_4_kernel);

pub(crate) fn launch(count: usize, stream: &CudaStream) -> CudaLaunchConfig<'_> {
    assert!(
        count > 0 && count <= u32::MAX as usize,
        "Proth120 WHIR: launch count outside 1..=u32::MAX"
    );
    CudaLaunchConfig::basic(count.div_ceil(BLOCK) as u32, BLOCK as u32, stream)
}

pub(crate) fn accumulate_base(
    memory: &(impl DeviceMatrixChunkImpl<PR> + ?Sized),
    setup: &(impl DeviceMatrixChunkImpl<PR> + ?Sized),
    pack_log2: u32,
    powers: &DeviceSlice<PR>,
    result: &mut DeviceSlice<PR>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let rows = memory.rows();
    assert!(
        rows.is_power_of_two() && rows == setup.rows(),
        "Proth120 WHIR: raw row geometry differs"
    );
    assert!(
        pack_log2 <= 4 && rows.trailing_zeros() + pack_log2 <= 26,
        "Proth120 WHIR: packed log exceeds 26"
    );
    assert!(
        memory.cols() > 0 && setup.cols() > 0,
        "Proth120 WHIR: raw columns must be nonzero"
    );
    let columns = [
        u32::try_from(memory.cols()).expect("Proth120 WHIR: memory columns overflow"),
        u32::try_from(setup.cols()).expect("Proth120 WHIR: setup columns overflow"),
    ];
    let pack = 1usize << pack_log2;
    assert_eq!(
        powers.len(),
        memory.cols().div_ceil(pack) + setup.cols().div_ceil(pack),
        "Proth120 WHIR: powers length differs from packed columns"
    );
    assert_eq!(
        result.len(),
        rows * pack,
        "Proth120 WHIR: accumulation length differs"
    );
    let a = memory.as_ptr_and_stride();
    let b = setup.as_ptr_and_stride();
    assert!(
        a.stride >= rows && b.stride >= rows,
        "Proth120 WHIR: raw column stride below rows"
    );
    let args = AccumulateBaseArguments::new(BaseColumnsMetadata {
        values: [a.ptr, b.ptr],
        columns,
        strides: [a.stride as u64, b.stride as u64],
        powers: powers.as_ptr(),
        result: result.as_mut_ptr(),
        log_rows: rows.trailing_zeros(),
        pack_log2,
    });
    AccumulateBaseFunction::default().launch(&launch(result.len(), stream), &args)
}

pub(crate) fn eq_from_point(
    point: &DeviceSlice<PR>,
    lo: &mut DeviceSlice<PR>,
    hi: &mut DeviceSlice<PR>,
    eq: &mut DeviceSlice<PR>,
    stream: &CudaStream,
) -> CudaResult<()> {
    let log_n = point.len();
    assert!(log_n <= 26, "Proth120 WHIR: eq log_n exceeds 26");
    let low_bits = log_n / 2;
    assert_eq!(
        lo.len(),
        1 << low_bits,
        "Proth120 WHIR: low eq table length differs"
    );
    assert_eq!(
        hi.len(),
        1 << (log_n - low_bits),
        "Proth120 WHIR: high eq table length differs"
    );
    assert_eq!(eq.len(), 1 << log_n, "Proth120 WHIR: eq length differs");
    EqSplitFunction::default().launch(
        &CudaLaunchConfig::basic(2, BLOCK as u32, stream),
        &EqSplitArguments::new(
            point.as_ptr(),
            log_n as u32,
            low_bits as u32,
            lo.as_mut_ptr(),
            hi.as_mut_ptr(),
        ),
    )?;
    EqJoinFunction::default().launch(
        &launch(eq.len(), stream),
        &EqJoinArguments::new(
            lo.as_ptr(),
            hi.as_ptr(),
            low_bits as u32,
            log_n as u32,
            eq.as_mut_ptr(),
        ),
    )
}

pub(crate) fn batched_opening(
    powers: &DeviceSlice<PR>,
    claims: &DeviceSlice<PR>,
    out: &mut DeviceSlice<PR>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert_eq!(
        powers.len(),
        claims.len(),
        "Proth120 WHIR: powers and claims lengths differ"
    );
    assert!(
        claims.len() <= u32::MAX as usize && out.len() == 1,
        "Proth120 WHIR: batched opening lengths invalid"
    );
    BatchedOpeningFunction::default().launch(
        &CudaLaunchConfig::basic(1, 1, stream),
        &BatchedOpeningArguments::new(
            powers.as_ptr(),
            claims.as_ptr(),
            claims.len() as u32,
            out.as_mut_ptr(),
        ),
    )
}

pub(crate) fn fold_adjacent(
    src: &DeviceSlice<PR>,
    dst: &mut DeviceSlice<PR>,
    challenge: &DeviceSlice<PR>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(
        src.len().is_power_of_two()
            && src.len() >= 2
            && dst.len() == src.len() / 2
            && challenge.len() == 1,
        "Proth120 WHIR: monomial fold lengths invalid"
    );
    FoldAdjacentFunction::default().launch(
        &launch(dst.len(), stream),
        &FoldAdjacentArguments::new(
            src.as_ptr(),
            dst.as_mut_ptr(),
            challenge.as_ptr(),
            dst.len() as u32,
        ),
    )
}

pub(crate) fn fold_adjacent_pair(
    src_a: &DeviceSlice<PR>,
    dst_a: &mut DeviceSlice<PR>,
    src_b: &DeviceSlice<PR>,
    dst_b: &mut DeviceSlice<PR>,
    challenge: &DeviceSlice<PR>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(
        src_a.len().is_power_of_two()
            && src_a.len() >= 2
            && src_b.len() == src_a.len()
            && dst_a.len() == src_a.len() / 2
            && dst_b.len() == dst_a.len()
            && challenge.len() == 1,
        "Proth120 WHIR: evaluation fold lengths invalid"
    );
    FoldAdjacentPairFunction::default().launch(
        &launch(dst_a.len(), stream),
        &FoldAdjacentPairArguments::new(
            src_a.as_ptr(),
            dst_a.as_mut_ptr(),
            src_b.as_ptr(),
            dst_b.as_mut_ptr(),
            challenge.as_ptr(),
            dst_a.len() as u32,
        ),
    )
}

pub(crate) fn whir_three_point_partials_len(half: usize) -> usize {
    if half <= BLOCK {
        0
    } else {
        half.div_ceil(BLOCK) * 3
    }
}

pub(crate) fn three_point(
    eval: &DeviceSlice<PR>,
    eq: &DeviceSlice<PR>,
    partials: &mut DeviceSlice<PR>,
    out: &mut DeviceSlice<PR>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(
        eval.len().is_power_of_two() && eval.len() >= 2 && eval.len() == eq.len() && out.len() == 3,
        "Proth120 WHIR: three point lengths invalid"
    );
    let half = eval.len() / 2;
    if half <= BLOCK {
        ThreePointCombinedFunction::default().launch(
            &CudaLaunchConfig::basic(1, BLOCK as u32, stream),
            &ThreePointCombinedArguments::new(
                eval.as_ptr(),
                eq.as_ptr(),
                out.as_mut_ptr(),
                half as u32,
            ),
        )
    } else {
        assert!(
            partials.len() >= whir_three_point_partials_len(half),
            "Proth120 WHIR: three point partials too short"
        );
        let blocks = half.div_ceil(BLOCK) as u32;
        ThreePointPartialsFunction::default().launch(
            &launch(half, stream),
            &ThreePointPartialsArguments::new(
                eval.as_ptr(),
                eq.as_ptr(),
                partials.as_mut_ptr(),
                half as u32,
            ),
        )?;
        ThreePointFinalizeFunction::default().launch(
            &CudaLaunchConfig::basic(1, BLOCK as u32, stream),
            &ThreePointFinalizeArguments::new(partials.as_ptr(), blocks, out.as_mut_ptr()),
        )
    }
}

pub(crate) fn monomial_eval_scratch_lens(count: usize) -> (usize, usize) {
    assert!(
        count.is_power_of_two(),
        "Proth120 WHIR: monomial count must be a power of two"
    );
    let large = count >= BLOCK * 32;
    let partials = if large { count / 32 } else { count };
    let sums = if partials > BLOCK {
        partials.div_ceil(BLOCK)
    } else {
        0
    };
    (partials, sums.max(usize::from(large)))
}

pub(crate) fn monomial_eval(
    src: &DeviceSlice<PR>,
    scratch0: &mut DeviceSlice<PR>,
    scratch1: &mut DeviceSlice<PR>,
    point: &DeviceSlice<PR>,
    out: &mut DeviceSlice<PR>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(
        src.len().is_power_of_two() && src.len() <= 1 << 26 && point.len() == 1 && out.len() == 1,
        "Proth120 WHIR: monomial evaluation lengths invalid"
    );
    let (partials, sums) = monomial_eval_scratch_lens(src.len());
    assert!(
        scratch0.len() >= partials && scratch1.len() >= sums,
        "Proth120 WHIR: monomial scratch too short"
    );
    if src.len() < BLOCK * 32 {
        MonomialEvalSmallFunction::default().launch(
            &launch(src.len(), stream),
            &MonomialEvalSmallArguments::new(
                src.as_ptr(),
                scratch0.as_mut_ptr(),
                point.as_ptr(),
                src.len().trailing_zeros(),
            ),
        )?;
    } else {
        gpu_ops::simple::pow(point, partials as u32, &mut scratch1[..1], stream)?;
        MonomialEvalFunction::default().launch(
            &launch(partials, stream),
            &MonomialEvalArguments::new(
                src.as_ptr(),
                scratch0.as_mut_ptr(),
                point.as_ptr(),
                scratch1.as_ptr(),
                src.len().trailing_zeros(),
            ),
        )?;
    }
    if partials <= BLOCK {
        SumFunction::default().launch(
            &CudaLaunchConfig::basic(1, BLOCK as u32, stream),
            &SumArguments::new(scratch0.as_ptr(), partials as u32, out.as_mut_ptr()),
        )
    } else {
        SumFunction::default().launch(
            &launch(partials, stream),
            &SumArguments::new(scratch0.as_ptr(), partials as u32, scratch1.as_mut_ptr()),
        )?;
        SumFunction::default().launch(
            &CudaLaunchConfig::basic(1, BLOCK as u32, stream),
            &SumArguments::new(scratch1.as_ptr(), sums as u32, out.as_mut_ptr()),
        )
    }
}

pub(crate) fn round_update(
    reductions: &mut DeviceSlice<PR>,
    seed: &mut DeviceSlice<u8>,
    coeffs: &mut DeviceSlice<PR>,
    challenge: &mut DeviceSlice<PR>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(
        reductions.len() == 3 && seed.len() == 32 && coeffs.len() == 3 && challenge.len() == 1,
        "Proth120 WHIR: round update lengths invalid"
    );
    RoundUpdateFunction::default().launch(
        &CudaLaunchConfig::basic(1, 1, stream),
        &RoundUpdateArguments::new(
            reductions.as_mut_ptr(),
            seed.as_mut_ptr(),
            coeffs.as_mut_ptr(),
            challenge.as_mut_ptr(),
        ),
    )
}

pub(crate) fn convert_tile_leaves(
    tile: &mut DeviceSlice<PR>,
    log_n: u32,
    log_v: u32,
    descriptor: TwiddleDescriptor,
    log_domain: u32,
    k0: u32,
    cosets: u32,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(
        (1..=4).contains(&log_v) && log_v < log_n && log_n <= log_domain,
        "Proth120 WHIR: tile leaf conversion geometry invalid"
    );
    assert_eq!(
        tile.len(),
        (cosets as usize) << log_n,
        "Proth120 WHIR: tile length differs from cosets << log_n"
    );
    let function = ConvertTileLeavesFunction(match log_v {
        1 => ab_pr_whir_convert_tile_leaves_1_kernel,
        2 => ab_pr_whir_convert_tile_leaves_2_kernel,
        3 => ab_pr_whir_convert_tile_leaves_3_kernel,
        _ => ab_pr_whir_convert_tile_leaves_4_kernel,
    });
    function.launch(
        &launch((cosets as usize) << (log_n - log_v), stream),
        &ConvertTileLeavesArguments::new(
            tile.as_mut_ptr(),
            log_n,
            descriptor,
            log_domain,
            k0,
            cosets,
        ),
    )
}

pub(crate) fn place_roots(
    retained: &DeviceSlice<Digest>,
    retained_stride: usize,
    log_lde: u32,
    roots: &mut DeviceSlice<Digest>,
    stream: &CudaStream,
) -> CudaResult<()> {
    assert!(
        (1..=31).contains(&log_lde) && retained_stride > 0,
        "Proth120 WHIR: place roots geometry invalid"
    );
    assert!(
        roots.len() == 1 << log_lde && retained.len() == roots.len() * retained_stride,
        "Proth120 WHIR: place roots lengths invalid"
    );
    PlaceRootsFunction::default().launch(
        &launch(roots.len(), stream),
        &PlaceRootsArguments::new(
            retained.as_ptr(),
            retained_stride as u64,
            log_lde,
            roots.as_mut_ptr(),
        ),
    )
}
