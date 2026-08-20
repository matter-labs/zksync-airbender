use serde::{Deserialize, Serialize};

pub const BABY_BEAR_ORDER: u128 = 0x7800_0001;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ReductionPath {
    U64RedWide,
    U96RedWideHighWord,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum InnerConvention {
    CanonicalResidue,
    SignSplitLazy,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ProductImmediateMode {
    ReduceProductThenMultiply,
    FusedThreeFactor,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum E4ProductPath {
    NoE4Product,
    CanonicalProductBeforeImmediate,
    FusedBfByE4Componentwise,
    FusedE4ByE4FlatQuarticUnreducedNonResidue,
    FusedMixedE4Products,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum MemberSign {
    Positive,
    Negative,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum InnerMemberKind {
    BfLinear,
    BfProduct,
    E4Linear,
    BfE4Product,
    E4Product,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct InnerMember {
    pub kind: InnerMemberKind,
    pub sign: MemberSign,
    pub immediate: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CapacityBound {
    pub reduction_path: ReductionPath,
    pub contribution_max: u128,
    pub raw_state_max: u128,
    pub reducer_safe_max: u128,
    pub required_contributions: u64,
    pub required_bits: u32,
    pub disposition: CapacityDisposition,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FeasibleCapacity {
    pub contributions_per_segment: u64,
    pub segment_count: u64,
    pub intermediate_reductions: u64,
    pub boundary_reductions: u64,
    pub high_word_max: u64,
    pub headroom_bits: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CapacityDisposition {
    Feasible(FeasibleCapacity),
    Infeasible {
        kind: String,
        required: u128,
        maximum: u128,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum InnerStateBounds {
    Canonical {
        state: CapacityBound,
    },
    SignSplit {
        positive: CapacityBound,
        negative: CapacityBound,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct InnerPolicyBound {
    pub convention: InnerConvention,
    pub product_mode: ProductImmediateMode,
    pub e4_product_path: E4ProductPath,
    pub reduction_path: ReductionPath,
    pub state_count: u32,
    pub contribution_max: u128,
    pub required_bits: u32,
    pub states: InnerStateBounds,
}

fn raw_state_max(path: ReductionPath) -> u128 {
    match path {
        ReductionPath::U64RedWide => u128::from(u64::MAX),
        ReductionPath::U96RedWideHighWord => (1u128 << 96) - 1,
    }
}

fn reducer_safe_max(path: ReductionPath) -> u128 {
    match path {
        ReductionPath::U64RedWide => u128::from(u64::MAX),
        ReductionPath::U96RedWideHighWord => BABY_BEAR_ORDER * (1u128 << 64) - 1,
    }
}

fn required_bits(value: u128) -> u32 {
    u128::BITS - value.leading_zeros()
}

fn feasible_details(
    contributions: &[u128],
    contribution_max: u128,
    safe_max: u128,
) -> CapacityDisposition {
    if contribution_max > safe_max {
        return CapacityDisposition::Infeasible {
            kind: "single_contribution_exceeds_reducer".to_owned(),
            required: contribution_max,
            maximum: safe_max,
        };
    }
    if contributions.is_empty() || contribution_max == 0 {
        return CapacityDisposition::Feasible(FeasibleCapacity {
            contributions_per_segment: 0,
            segment_count: 0,
            intermediate_reductions: 0,
            boundary_reductions: 0,
            high_word_max: 0,
            headroom_bits: required_bits(safe_max),
        });
    }
    let contributions_per_segment = u64::try_from(safe_max / contribution_max).unwrap_or(u64::MAX);
    let mut segment_count = 0u64;
    let mut segment_sum = 0u128;
    let mut maximum_segment_sum = 0u128;
    for contribution in contributions {
        if segment_sum != 0 && segment_sum + contribution > safe_max {
            maximum_segment_sum = maximum_segment_sum.max(segment_sum);
            segment_count += 1;
            segment_sum = 0;
        }
        segment_sum += contribution;
    }
    if segment_sum != 0 {
        maximum_segment_sum = maximum_segment_sum.max(segment_sum);
        segment_count += 1;
    }
    CapacityDisposition::Feasible(FeasibleCapacity {
        contributions_per_segment,
        segment_count,
        intermediate_reductions: segment_count.saturating_sub(1),
        boundary_reductions: segment_count,
        high_word_max: u64::try_from(maximum_segment_sum >> 64)
            .expect("reducer-safe high word fits u64"),
        headroom_bits: required_bits(safe_max).saturating_sub(required_bits(maximum_segment_sum)),
    })
}

fn state_bound(path: ReductionPath, contributions: &[u128]) -> CapacityBound {
    let contribution_max = contributions.iter().copied().max().unwrap_or(0);
    let total = contributions.iter().copied().sum();
    let safe_max = reducer_safe_max(path);
    CapacityBound {
        reduction_path: path,
        contribution_max,
        raw_state_max: raw_state_max(path),
        reducer_safe_max: safe_max,
        required_contributions: contributions.len() as u64,
        required_bits: required_bits(total),
        disposition: feasible_details(contributions, contribution_max, safe_max),
    }
}

fn uniform_state_bound(path: ReductionPath, count: u64, contribution: u128) -> CapacityBound {
    let safe_max = reducer_safe_max(path);
    let total = contribution * u128::from(count);
    let disposition = if contribution > safe_max {
        CapacityDisposition::Infeasible {
            kind: "single_contribution_exceeds_reducer".to_owned(),
            required: contribution,
            maximum: safe_max,
        }
    } else if count == 0 || contribution == 0 {
        CapacityDisposition::Feasible(FeasibleCapacity {
            contributions_per_segment: 0,
            segment_count: 0,
            intermediate_reductions: 0,
            boundary_reductions: 0,
            high_word_max: 0,
            headroom_bits: required_bits(safe_max),
        })
    } else {
        let per_segment = u64::try_from(safe_max / contribution).unwrap_or(u64::MAX);
        let segment_count = count.div_ceil(per_segment);
        let maximum_segment_contributions = count.min(per_segment);
        let maximum_segment_sum = contribution * u128::from(maximum_segment_contributions);
        CapacityDisposition::Feasible(FeasibleCapacity {
            contributions_per_segment: per_segment,
            segment_count,
            intermediate_reductions: segment_count.saturating_sub(1),
            boundary_reductions: segment_count,
            high_word_max: u64::try_from(maximum_segment_sum >> 64)
                .expect("reducer-safe high word fits u64"),
            headroom_bits: required_bits(safe_max)
                .saturating_sub(required_bits(maximum_segment_sum)),
        })
    };
    CapacityBound {
        reduction_path: path,
        contribution_max: contribution,
        raw_state_max: raw_state_max(path),
        reducer_safe_max: safe_max,
        required_contributions: count,
        required_bits: required_bits(total),
        disposition,
    }
}

pub fn outer_fold_bounds(bf_atoms: u64) -> [CapacityBound; 2] {
    let contribution = (BABY_BEAR_ORDER - 1).pow(2);
    [
        uniform_state_bound(ReductionPath::U64RedWide, bf_atoms, contribution),
        uniform_state_bound(ReductionPath::U96RedWideHighWord, bf_atoms, contribution),
    ]
}

fn sign_split_contribution(member: &InnerMember, mode: ProductImmediateMode) -> u128 {
    let immediate = u128::from(member.immediate);
    match (member.kind, mode) {
        (InnerMemberKind::BfProduct, ProductImmediateMode::FusedThreeFactor) => {
            immediate * (BABY_BEAR_ORDER - 1).pow(2)
        }
        (InnerMemberKind::BfE4Product, ProductImmediateMode::FusedThreeFactor) => {
            immediate * (BABY_BEAR_ORDER - 1).pow(2)
        }
        (InnerMemberKind::E4Product, ProductImmediateMode::FusedThreeFactor) => {
            // Flat quartic schoolbook multiplication with the non-residue
            // factors left unreduced has per-output coefficient sums
            // [34, 14, 24, 4]. The first output therefore establishes the
            // exact worst-limb representation bound before the immediate.
            immediate * 34 * (BABY_BEAR_ORDER - 1).pow(2)
        }
        _ => immediate * (BABY_BEAR_ORDER - 1),
    }
}

pub fn inner_group_bounds(members: &[InnerMember]) -> Vec<InnerPolicyBound> {
    let has_bf_e4_product = members
        .iter()
        .any(|member| member.kind == InnerMemberKind::BfE4Product);
    let has_e4_e4_product = members
        .iter()
        .any(|member| member.kind == InnerMemberKind::E4Product);
    let mut result = Vec::with_capacity(8);
    for convention in [
        InnerConvention::CanonicalResidue,
        InnerConvention::SignSplitLazy,
    ] {
        for product_mode in [
            ProductImmediateMode::ReduceProductThenMultiply,
            ProductImmediateMode::FusedThreeFactor,
        ] {
            for reduction_path in [ReductionPath::U64RedWide, ReductionPath::U96RedWideHighWord] {
                let states = match convention {
                    InnerConvention::CanonicalResidue => {
                        let contributions = vec![BABY_BEAR_ORDER - 1; members.len()];
                        InnerStateBounds::Canonical {
                            state: state_bound(reduction_path, &contributions),
                        }
                    }
                    InnerConvention::SignSplitLazy => {
                        let mut positive = Vec::new();
                        let mut negative = Vec::new();
                        for member in members {
                            let contribution = sign_split_contribution(member, product_mode);
                            match member.sign {
                                MemberSign::Positive => positive.push(contribution),
                                MemberSign::Negative => negative.push(contribution),
                            }
                        }
                        InnerStateBounds::SignSplit {
                            positive: state_bound(reduction_path, &positive),
                            negative: state_bound(reduction_path, &negative),
                        }
                    }
                };
                let (state_count, contribution_max, bits) = match &states {
                    InnerStateBounds::Canonical { state } => {
                        (1, state.contribution_max, state.required_bits)
                    }
                    InnerStateBounds::SignSplit { positive, negative } => (
                        2,
                        positive.contribution_max.max(negative.contribution_max),
                        positive.required_bits.max(negative.required_bits),
                    ),
                };
                result.push(InnerPolicyBound {
                    convention,
                    product_mode,
                    e4_product_path: match (
                        has_bf_e4_product,
                        has_e4_e4_product,
                        convention,
                        product_mode,
                    ) {
                        (false, false, _, _) => E4ProductPath::NoE4Product,
                        (
                            _,
                            _,
                            InnerConvention::CanonicalResidue,
                            ProductImmediateMode::ReduceProductThenMultiply
                            | ProductImmediateMode::FusedThreeFactor,
                        )
                        | (
                            _,
                            _,
                            InnerConvention::SignSplitLazy,
                            ProductImmediateMode::ReduceProductThenMultiply,
                        ) => E4ProductPath::CanonicalProductBeforeImmediate,
                        (
                            true,
                            false,
                            InnerConvention::SignSplitLazy,
                            ProductImmediateMode::FusedThreeFactor,
                        ) => E4ProductPath::FusedBfByE4Componentwise,
                        (
                            false,
                            true,
                            InnerConvention::SignSplitLazy,
                            ProductImmediateMode::FusedThreeFactor,
                        ) => E4ProductPath::FusedE4ByE4FlatQuarticUnreducedNonResidue,
                        (
                            true,
                            true,
                            InnerConvention::SignSplitLazy,
                            ProductImmediateMode::FusedThreeFactor,
                        ) => E4ProductPath::FusedMixedE4Products,
                    },
                    reduction_path,
                    state_count,
                    contribution_max,
                    required_bits: bits,
                    states,
                });
            }
        }
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    fn banked_bf_product(immediate: u128) -> InnerMember {
        InnerMember {
            kind: InnerMemberKind::BfProduct,
            sign: MemberSign::Positive,
            immediate: immediate as u32,
        }
    }

    fn banked_e4_product(immediate: u128) -> InnerMember {
        InnerMember {
            kind: InnerMemberKind::E4Product,
            sign: MemberSign::Positive,
            immediate: immediate as u32,
        }
    }

    fn banked_bf_e4_product(immediate: u128) -> InnerMember {
        InnerMember {
            kind: InnerMemberKind::BfE4Product,
            sign: MemberSign::Positive,
            immediate: immediate as u32,
        }
    }

    fn adversarial_signed_members() -> Vec<InnerMember> {
        [
            MemberSign::Positive,
            MemberSign::Negative,
            MemberSign::Positive,
            MemberSign::Negative,
            MemberSign::Positive,
        ]
        .into_iter()
        .map(|sign| InnerMember {
            kind: InnerMemberKind::BfLinear,
            sign,
            immediate: 1,
        })
        .collect()
    }

    #[test]
    fn outer_bounds_distinguish_raw_u96_from_named_reducer_capacity() {
        let [u64_bound, u96_bound] = outer_fold_bounds(1_442);
        let CapacityDisposition::Feasible(u64_fit) = &u64_bound.disposition else {
            panic!("outer u64 bound must be feasible");
        };
        assert_eq!(u64_fit.contributions_per_segment, 4);
        assert_eq!(u64_fit.segment_count, 361);
        assert!(u96_bound.raw_state_max > u96_bound.reducer_safe_max);
        let CapacityDisposition::Feasible(u96_fit) = &u96_bound.disposition else {
            panic!("outer u96 bound must be feasible");
        };
        assert_eq!(u96_fit.segment_count, 1);
        assert!(u128::from(u96_fit.high_word_max) < BABY_BEAR_ORDER);
    }

    #[test]
    fn reducer_boundary_plus_one_is_not_safe() {
        let contribution = (BABY_BEAR_ORDER - 1).pow(2);
        for capacity in [u128::from(u64::MAX), BABY_BEAR_ORDER * (1u128 << 64) - 1] {
            let fit = capacity / contribution;
            assert!(fit * contribution <= capacity);
            assert!((fit + 1) * contribution > capacity);
        }
    }

    #[test]
    fn repeated_addition_independently_reaches_the_u64_boundary() {
        let contribution = (BABY_BEAR_ORDER - 1).pow(2);
        let fit = u128::from(u64::MAX) / contribution;
        let mut sum = 0u128;
        for _ in 0..fit {
            sum = sum.checked_add(contribution).unwrap();
            assert!(sum <= u128::from(u64::MAX));
        }
        assert!(sum.checked_add(contribution).unwrap() > u128::from(u64::MAX));
    }

    #[test]
    fn canonical_and_sign_split_have_one_and_two_states() {
        let bounds = inner_group_bounds(&adversarial_signed_members());
        assert!(bounds
            .iter()
            .all(|bound| match (&bound.convention, &bound.states) {
                (InnerConvention::CanonicalResidue, InnerStateBounds::Canonical { .. }) => {
                    bound.state_count == 1
                }
                (InnerConvention::SignSplitLazy, InnerStateBounds::SignSplit { .. }) => {
                    bound.state_count == 2
                }
                _ => false,
            }));
    }

    #[test]
    fn sign_split_never_cancels_positive_and_negative_capacity() {
        let bounds = inner_group_bounds(&adversarial_signed_members());
        let bound = bounds
            .iter()
            .find(|bound| {
                bound.convention == InnerConvention::SignSplitLazy
                    && bound.product_mode == ProductImmediateMode::ReduceProductThenMultiply
                    && bound.reduction_path == ReductionPath::U64RedWide
            })
            .unwrap();
        let InnerStateBounds::SignSplit { positive, negative } = &bound.states else {
            panic!("expected two sign-split states");
        };
        assert_eq!(positive.required_contributions, 3);
        assert_eq!(negative.required_contributions, 2);
    }

    #[test]
    fn banked_product_modes_have_square_and_cube_bounds() {
        let bounds = inner_group_bounds(&[banked_bf_product(BABY_BEAR_ORDER - 1)]);
        assert!(bounds.iter().any(|bound| {
            bound.convention == InnerConvention::SignSplitLazy
                && bound.product_mode == ProductImmediateMode::ReduceProductThenMultiply
                && bound.contribution_max == (BABY_BEAR_ORDER - 1).pow(2)
        }));
        assert!(bounds.iter().any(|bound| {
            bound.convention == InnerConvention::SignSplitLazy
                && bound.product_mode == ProductImmediateMode::FusedThreeFactor
                && bound.contribution_max == (BABY_BEAR_ORDER - 1).pow(3)
        }));
    }

    #[test]
    fn fused_e4_product_uses_the_flat_quartic_non_residue_limb_bound() {
        let limb = BABY_BEAR_ORDER - 1;
        let output_limb_coefficients = [
            1u128 + 11 + 11 + 11,
            1 + 1 + 1 + 11,
            1 + 11 + 1 + 11,
            1 + 1 + 1 + 1,
        ];
        let independently_computed_limb_max = output_limb_coefficients
            .into_iter()
            .map(|coefficient_sum| coefficient_sum * limb * limb)
            .max()
            .unwrap();
        let immediate = 5u128;
        let bounds = inner_group_bounds(&[banked_e4_product(immediate)]);
        let fused = bounds
            .iter()
            .find(|bound| {
                bound.convention == InnerConvention::SignSplitLazy
                    && bound.product_mode == ProductImmediateMode::FusedThreeFactor
                    && bound.reduction_path == ReductionPath::U96RedWideHighWord
            })
            .unwrap();
        assert_eq!(
            fused.contribution_max,
            immediate * independently_computed_limb_max
        );
        assert_eq!(
            fused.e4_product_path,
            E4ProductPath::FusedE4ByE4FlatQuarticUnreducedNonResidue
        );
    }

    #[test]
    fn fused_bf_by_e4_product_has_one_base_product_per_output_limb() {
        let immediate = 5u128;
        let bounds = inner_group_bounds(&[banked_bf_e4_product(immediate)]);
        let fused = bounds
            .iter()
            .find(|bound| {
                bound.convention == InnerConvention::SignSplitLazy
                    && bound.product_mode == ProductImmediateMode::FusedThreeFactor
                    && bound.reduction_path == ReductionPath::U96RedWideHighWord
            })
            .unwrap();
        assert_eq!(
            fused.contribution_max,
            immediate * (BABY_BEAR_ORDER - 1).pow(2)
        );
        assert_eq!(
            fused.e4_product_path,
            E4ProductPath::FusedBfByE4Componentwise
        );
    }

    #[test]
    fn one_contribution_larger_than_u64_capacity_is_typed_infeasible_data() {
        let bounds = inner_group_bounds(&[banked_bf_product(5)]);
        let fused_u64 = bounds
            .iter()
            .find(|bound| {
                bound.convention == InnerConvention::SignSplitLazy
                    && bound.product_mode == ProductImmediateMode::FusedThreeFactor
                    && bound.reduction_path == ReductionPath::U64RedWide
            })
            .unwrap();
        let InnerStateBounds::SignSplit { positive, .. } = &fused_u64.states else {
            panic!("expected sign-split policy");
        };
        assert!(matches!(
            &positive.disposition,
            CapacityDisposition::Infeasible {
                kind,
                required,
                maximum,
            } if kind == "single_contribution_exceeds_reducer" && required > maximum
        ));
    }

    #[test]
    fn exact_u64_boundary_uses_one_segment_and_plus_one_uses_two() {
        let fit = (u128::from(u64::MAX) / (BABY_BEAR_ORDER - 1).pow(2)) as usize;
        let at_boundary = vec![banked_bf_product(BABY_BEAR_ORDER - 1); fit];
        let over_boundary = vec![banked_bf_product(BABY_BEAR_ORDER - 1); fit + 1];
        let segments = |members: &[InnerMember]| {
            let bound = inner_group_bounds(members)
                .into_iter()
                .find(|bound| {
                    bound.convention == InnerConvention::SignSplitLazy
                        && bound.product_mode == ProductImmediateMode::ReduceProductThenMultiply
                        && bound.reduction_path == ReductionPath::U64RedWide
                })
                .unwrap();
            let InnerStateBounds::SignSplit { positive, .. } = bound.states else {
                panic!("expected sign-split policy");
            };
            let CapacityDisposition::Feasible(fit) = positive.disposition else {
                panic!("unit-immediate products must fit u64");
            };
            fit.segment_count
        };
        assert_eq!(segments(&at_boundary), 1);
        assert_eq!(segments(&over_boundary), 2);
    }
}
