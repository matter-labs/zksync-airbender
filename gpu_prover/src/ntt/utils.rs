#[allow(non_camel_case_types)]
#[allow(clippy::upper_case_acronyms)]
#[derive(Copy, Clone, Debug, PartialEq)]
pub(crate) enum N2B_LAUNCH {
    FINAL_7_WARP,
    FINAL_8_WARP,
    FINAL_9_TO_12_BLOCK,
    NONFINAL_7_OR_8_BLOCK,
}

#[allow(non_camel_case_types)]
#[allow(clippy::upper_case_acronyms)]
#[derive(Copy, Clone, Debug, PartialEq)]
pub(crate) enum B2N_LAUNCH {
    INITIAL_7_WARP,
    INITIAL_8_WARP,
    INITIAL_9_TO_12_BLOCK,
    NONINITIAL_7_OR_8_BLOCK,
}

// Kernel plans for sizes 2^16..24.
// I'd rather use a hashmap containing vectors of different sizes instead of a list of fixed-size lists,
// but Rust didn't let me declare hashmaps or vectors const.
#[allow(non_camel_case_types)]
pub(crate) type N2B_Plan = [Option<(N2B_LAUNCH, u32)>; 3];

pub(crate) const STAGE_PLANS_N2B: [N2B_Plan; 9] = [
    [
        Some((N2B_LAUNCH::NONFINAL_7_OR_8_BLOCK, 8)),
        Some((N2B_LAUNCH::FINAL_8_WARP, 8)),
        None,
    ],
    [
        Some((N2B_LAUNCH::NONFINAL_7_OR_8_BLOCK, 8)),
        Some((N2B_LAUNCH::FINAL_9_TO_12_BLOCK, 9)),
        None,
    ],
    [
        Some((N2B_LAUNCH::NONFINAL_7_OR_8_BLOCK, 8)),
        Some((N2B_LAUNCH::FINAL_9_TO_12_BLOCK, 10)),
        None,
    ],
    [
        Some((N2B_LAUNCH::NONFINAL_7_OR_8_BLOCK, 8)),
        Some((N2B_LAUNCH::FINAL_9_TO_12_BLOCK, 11)),
        None,
    ],
    [
        Some((N2B_LAUNCH::NONFINAL_7_OR_8_BLOCK, 8)),
        Some((N2B_LAUNCH::FINAL_9_TO_12_BLOCK, 12)),
        None,
    ],
    [
        Some((N2B_LAUNCH::NONFINAL_7_OR_8_BLOCK, 7)),
        Some((N2B_LAUNCH::NONFINAL_7_OR_8_BLOCK, 7)),
        Some((N2B_LAUNCH::FINAL_7_WARP, 7)),
    ],
    [
        Some((N2B_LAUNCH::NONFINAL_7_OR_8_BLOCK, 7)),
        Some((N2B_LAUNCH::NONFINAL_7_OR_8_BLOCK, 7)),
        Some((N2B_LAUNCH::FINAL_8_WARP, 8)),
    ],
    [
        Some((N2B_LAUNCH::NONFINAL_7_OR_8_BLOCK, 7)),
        Some((N2B_LAUNCH::NONFINAL_7_OR_8_BLOCK, 8)),
        Some((N2B_LAUNCH::FINAL_8_WARP, 8)),
    ],
    [
        Some((N2B_LAUNCH::NONFINAL_7_OR_8_BLOCK, 8)),
        Some((N2B_LAUNCH::NONFINAL_7_OR_8_BLOCK, 8)),
        Some((N2B_LAUNCH::FINAL_8_WARP, 8)),
    ],
];

#[allow(non_camel_case_types)]
pub(crate) type B2N_Plan = [Option<(B2N_LAUNCH, u32)>; 3];

pub(crate) const STAGE_PLANS_B2N: [B2N_Plan; 9] = [
    [
        Some((B2N_LAUNCH::INITIAL_8_WARP, 8)),
        Some((B2N_LAUNCH::NONINITIAL_7_OR_8_BLOCK, 8)),
        None,
    ],
    [
        Some((B2N_LAUNCH::INITIAL_9_TO_12_BLOCK, 9)),
        Some((B2N_LAUNCH::NONINITIAL_7_OR_8_BLOCK, 8)),
        None,
    ],
    [
        Some((B2N_LAUNCH::INITIAL_9_TO_12_BLOCK, 10)),
        Some((B2N_LAUNCH::NONINITIAL_7_OR_8_BLOCK, 8)),
        None,
    ],
    [
        Some((B2N_LAUNCH::INITIAL_9_TO_12_BLOCK, 11)),
        Some((B2N_LAUNCH::NONINITIAL_7_OR_8_BLOCK, 8)),
        None,
    ],
    [
        Some((B2N_LAUNCH::INITIAL_9_TO_12_BLOCK, 12)),
        Some((B2N_LAUNCH::NONINITIAL_7_OR_8_BLOCK, 8)),
        None,
    ],
    [
        Some((B2N_LAUNCH::INITIAL_7_WARP, 7)),
        Some((B2N_LAUNCH::NONINITIAL_7_OR_8_BLOCK, 7)),
        Some((B2N_LAUNCH::NONINITIAL_7_OR_8_BLOCK, 7)),
    ],
    [
        Some((B2N_LAUNCH::INITIAL_8_WARP, 8)),
        Some((B2N_LAUNCH::NONINITIAL_7_OR_8_BLOCK, 7)),
        Some((B2N_LAUNCH::NONINITIAL_7_OR_8_BLOCK, 7)),
    ],
    [
        Some((B2N_LAUNCH::INITIAL_8_WARP, 8)),
        Some((B2N_LAUNCH::NONINITIAL_7_OR_8_BLOCK, 8)),
        Some((B2N_LAUNCH::NONINITIAL_7_OR_8_BLOCK, 7)),
    ],
    [
        Some((B2N_LAUNCH::INITIAL_8_WARP, 8)),
        Some((B2N_LAUNCH::NONINITIAL_7_OR_8_BLOCK, 8)),
        Some((B2N_LAUNCH::NONINITIAL_7_OR_8_BLOCK, 8)),
    ],
];

pub(crate) fn get_main_to_coset_launch_chain(
    log_n: usize,
) -> (Vec<(N2B_LAUNCH, u32)>, Vec<(B2N_LAUNCH, u32)>) {
    assert!(log_n >= 16);
    let n2b_plan = &STAGE_PLANS_N2B[log_n - 16];
    let b2n_plan = &STAGE_PLANS_B2N[log_n - 16];
    // For convenience, filter out the Nones.
    let n2b_launches: Vec<_> = n2b_plan.iter().filter_map(|&x| x).collect();
    let b2n_launches: Vec<_> = b2n_plan.iter().filter_map(|&x| x).collect();
    assert_eq!(n2b_launches.len(), b2n_launches.len());
    (n2b_launches, b2n_launches)
}

// Each block can process up to REAL_COLS_PER_BLOCK real columns
// and/or COMPLEX_COLS_PER_BLOCK complex columns, which amortizes
// twiddles loads. However, the actual optimal batch size per launch
// may be less than these values, because smaller batches improve the
// chance data values persist in L2.
// In practice, it's a tradeoff and batch size should be tuned.
pub const REAL_COLS_PER_BLOCK: u32 = 8;
pub const COMPLEX_COLS_PER_BLOCK: u32 = 4;
