use std::collections::BTreeMap;
use std::mem::{align_of, offset_of, size_of};
use std::ops::Range;
use std::sync::Arc;

use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::CudaResult;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_gkr_compiler::{
    CoeffProduct, CoefficientRecipeId, NormalizedCoefficientRecipe, WindowCoefficientPlan,
};
use gpu_prover_context::transfer::Transfer;
#[cfg(test)]
use gpu_prover_context::transfer::TransferKeepalive;
use gpu_prover_context::ProverContext;

use crate::backward::window::coefficient_bank::{
    coefficient_bank_challenge_slot, BWD_COEFF_CHALLENGE_CLAIM_BATCHING,
};
use crate::proth120::programs::GkrProgramsPr;
use crate::upstream::{Field, PrimeField, PR};

pub(crate) const PR_COEFF_CHALLENGES: usize = 9;
pub(crate) const PR_COEFF_CHALLENGE_ABSENT: u8 = 0xff;
#[cfg(test)]
pub(crate) const PR_EVAL_COEFFICIENTS_ARGUMENT_BYTES: usize = size_of::<CoeffFillDescPr>();
const PR_COEFF_FILL_BLOCK_THREADS: u32 = 128;
const PR_COEFF_FILL_WARPS: u32 = 4;
const PR_COEFF_RECIPE_WORDS: usize = 2;
const PR_COEFF_MONOMIAL_WORDS: usize = 2;

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct CoeffRecipePr {
    pub monomial_offset: u32,
    pub monomial_count: u32,
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct CoeffMonomialPr {
    pub batch_power: u16,
    pub challenge_idx_0: u8,
    pub challenge_idx_1: u8,
    pub power_0: u8,
    pub power_1: u8,
    pub _pad: [u8; 2],
}

impl Default for CoeffMonomialPr {
    fn default() -> Self {
        Self {
            batch_power: 0,
            challenge_idx_0: PR_COEFF_CHALLENGE_ABSENT,
            challenge_idx_1: PR_COEFF_CHALLENGE_ABSENT,
            power_0: 0,
            power_1: 0,
            _pad: [0; 2],
        }
    }
}

impl CoeffMonomialPr {
    fn key(&self) -> (u16, u8, u8, u8, u8) {
        (
            self.batch_power,
            self.challenge_idx_0,
            self.power_0,
            self.challenge_idx_1,
            self.power_1,
        )
    }

    fn from_key(key: (u16, u8, u8, u8, u8)) -> Self {
        let (batch_power, challenge_idx_0, power_0, challenge_idx_1, power_1) = key;
        Self {
            batch_power,
            challenge_idx_0,
            challenge_idx_1,
            power_0,
            power_1,
            _pad: [0; 2],
        }
    }

    fn words(&self) -> [u32; PR_COEFF_MONOMIAL_WORDS] {
        [
            u32::from(self.batch_power)
                | u32::from(self.challenge_idx_0) << 16
                | u32::from(self.challenge_idx_1) << 24,
            u32::from(self.power_0) | u32::from(self.power_1) << 8,
        ]
    }
}

impl CoeffRecipePr {
    fn words(&self) -> [u32; PR_COEFF_RECIPE_WORDS] {
        [self.monomial_offset, self.monomial_count]
    }
}

#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct CoeffFillDescPr {
    pub recipes: *const CoeffRecipePr,
    pub monomials: *const CoeffMonomialPr,
    pub monomial_coeffs: *const PR,
    pub challenges: *const PR,
    pub claim_batching: *const PR,
    pub coefficients: *mut PR,
    pub recipe_first: u32,
    pub recipe_count: u32,
}

const _: () = {
    assert!(size_of::<PR>() == 16);
    assert!(size_of::<CoeffRecipePr>() == 8 && align_of::<CoeffRecipePr>() == 4);
    assert!(offset_of!(CoeffRecipePr, monomial_count) == 4);
    assert!(size_of::<CoeffMonomialPr>() == 8 && align_of::<CoeffMonomialPr>() == 2);
    assert!(offset_of!(CoeffMonomialPr, challenge_idx_0) == 2);
    assert!(offset_of!(CoeffMonomialPr, challenge_idx_1) == 3);
    assert!(offset_of!(CoeffMonomialPr, power_0) == 4);
    assert!(offset_of!(CoeffMonomialPr, power_1) == 5);
    assert!(size_of::<CoeffFillDescPr>() == 56 && align_of::<CoeffFillDescPr>() == 8);
    assert!(offset_of!(CoeffFillDescPr, monomials) == 8);
    assert!(offset_of!(CoeffFillDescPr, monomial_coeffs) == 16);
    assert!(offset_of!(CoeffFillDescPr, challenges) == 24);
    assert!(offset_of!(CoeffFillDescPr, claim_batching) == 32);
    assert!(offset_of!(CoeffFillDescPr, coefficients) == 40);
    assert!(offset_of!(CoeffFillDescPr, recipe_first) == 48);
    assert!(offset_of!(CoeffFillDescPr, recipe_count) == 52);
    assert!(PR_COEFF_RECIPE_WORDS * size_of::<u32>() == size_of::<CoeffRecipePr>());
    assert!(PR_COEFF_MONOMIAL_WORDS * size_of::<u32>() == size_of::<CoeffMonomialPr>());
    assert!(BWD_COEFF_CHALLENGE_CLAIM_BATCHING as usize == PR_COEFF_CHALLENGES);
};

cuda_kernel!(
    PrEvalCoefficients,
    ab_pr_gkr_bwd_eval_coefficients_kernel(desc: CoeffFillDescPr)
);

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CoefficientLayerRangesPr {
    pub recipe_first: u32,
    pub r0_len: u32,
    pub continuation_len: u32,
    pub r0_immediates: Range<u32>,
    pub continuation_immediates: Range<u32>,
}

impl CoefficientLayerRangesPr {
    pub(crate) fn len(&self) -> u32 {
        self.r0_len + self.continuation_len
    }
}

#[derive(Clone, Debug, Default)]
pub(crate) struct CoefficientTablesHostPr {
    pub recipes: Vec<CoeffRecipePr>,
    pub monomials: Vec<CoeffMonomialPr>,
    pub monomial_coeffs: Vec<PR>,
    pub immediates: Vec<PR>,
    pub layers: Vec<CoefficientLayerRangesPr>,
}

fn translate_product(
    product: &CoeffProduct,
    recipe_index: usize,
    product_index: usize,
) -> CoeffMonomialPr {
    let mut exponents: BTreeMap<u8, u32> = BTreeMap::new();
    for challenge in &product.challenges {
        let (slot, power) = coefficient_bank_challenge_slot(&challenge.0)
            .expect("Proth120 coefficient challenge must be supported");
        *exponents.entry(slot).or_default() += power;
    }
    exponents.retain(|_, exponent| *exponent != 0);
    let batch = exponents
        .remove(&BWD_COEFF_CHALLENGE_CLAIM_BATCHING)
        .unwrap_or(0);
    assert!(
        batch <= u32::from(u16::MAX),
        "Proth120 binding BatchPowerOverflow: recipe={:?}, product={:?}, power={:?}",
        recipe_index,
        product_index,
        batch
    );
    assert!(
        exponents.len() <= 2,
        "Proth120 binding TooManyDistinctChallenges: recipe={:?}, product={:?}, distinct={:?}",
        recipe_index,
        product_index,
        exponents.len()
    );
    let mut monomial = CoeffMonomialPr {
        batch_power: batch as u16,
        ..CoeffMonomialPr::default()
    };
    for (position, (slot, exponent)) in exponents.into_iter().enumerate() {
        assert!(
            usize::from(slot) < PR_COEFF_CHALLENGES,
            "Proth120 coefficient challenge slot {slot} is outside the packed challenges"
        );
        assert!(exponent <= u32::from(u8::MAX),
            "Proth120 binding ExponentOverflow: recipe={:?}, product={:?}, slot={:?}, exponent={:?}", recipe_index, product_index, slot, exponent
        );
        if position == 0 {
            monomial.challenge_idx_0 = slot;
            monomial.power_0 = exponent as u8;
        } else {
            monomial.challenge_idx_1 = slot;
            monomial.power_1 = exponent as u8;
        }
    }
    monomial
}

fn translate_recipe(
    recipe: &NormalizedCoefficientRecipe,
    recipe_index: usize,
    top_bits: &[u32],
    keep_zeros: bool,
) -> Vec<(PR, CoeffMonomialPr)> {
    let mut merged: BTreeMap<(u16, u8, u8, u8, u8), PR> = BTreeMap::new();
    for (product_index, product) in recipe.terms.iter().enumerate() {
        let monomial = translate_product(product, recipe_index, product_index);
        let mut scalar = PR::from_u128_with_reduction(product.scalar);
        for reference in &product.inits_and_teardowns_top_bits {
            let bits = top_bits
                .get(reference.set_index)
                .copied()
                .unwrap_or_else(|| {
                    panic!(
                        "Proth120 binding MissingTopBits: recipe={:?}, product={:?}, set_index={:?}, available={:?}", recipe_index, product_index, reference.set_index, top_bits.len()
                    )
                });
            let shifted = bits.checked_shl(reference.shift).unwrap_or(0);
            scalar.mul_assign(&PR::from_u32_with_reduction(shifted));
        }
        merged
            .entry(monomial.key())
            .and_modify(|value| {
                value.add_assign(&scalar);
            })
            .or_insert(scalar);
    }
    merged
        .into_iter()
        .filter(|(_, scalar)| keep_zeros || !scalar.is_zero())
        .map(|(key, scalar)| (scalar, CoeffMonomialPr::from_key(key)))
        .collect()
}

impl CoefficientTablesHostPr {
    pub(crate) fn build(programs: &GkrProgramsPr, top_bits: &[u32]) -> Self {
        Self::build_with(programs, top_bits, false)
    }

    fn build_with(programs: &GkrProgramsPr, top_bits: &[u32], keep_zeros: bool) -> Self {
        let layers = programs.r0.len();
        assert_eq!(
            programs.continuations.layers.len(),
            layers,
            "Proth120 coefficient tables need one continuation program per R0 layer"
        );
        assert_eq!(
            programs.main_continuation_window.len(),
            layers,
            "Proth120 coefficient tables need one main continuation window per layer"
        );
        assert_eq!(
            programs.main_tail.len(),
            layers,
            "Proth120 coefficient tables need one main tail per layer"
        );
        let mut tables = Self::default();
        for layer in 0..layers {
            let window = &programs.r0[layer].window;
            let continuation = &programs.continuations.layers[layer].coefficients;
            assert_eq!(
                continuation.immediates, programs.main_continuation_window[layer].immediates,
                "Proth120 layer {layer} continuation immediates differ from the main continuation window"
            );
            assert_eq!(
                continuation.immediates, programs.main_tail[layer].immediates,
                "Proth120 layer {layer} continuation immediates differ from the main tail"
            );
            let recipe_first = tables.recipes.len();
            tables.push_literals();
            for (index, plan) in window.coefficient_plans.iter().enumerate() {
                let WindowCoefficientPlan::Direct(recipe) = plan else {
                    panic!("Proth120 R0 layer {layer} plan {index} must be Direct");
                };
                tables.push_recipe(recipe, index, top_bits, layer, keep_zeros);
            }
            let r0_len = tables.recipes.len() - recipe_first;
            tables.push_literals();
            for (index, recipe) in continuation.coefficients.iter().enumerate() {
                tables.push_recipe(recipe, index, top_bits, layer, keep_zeros);
            }
            let continuation_len = tables.recipes.len() - recipe_first - r0_len;
            assert!(
                r0_len >= CoefficientRecipeId::RESERVED as usize
                    && continuation_len >= CoefficientRecipeId::RESERVED as usize
            );
            let r0_immediates = tables.push_immediates(&window.immediates);
            let continuation_immediates = tables.push_immediates(&continuation.immediates);
            tables.layers.push(CoefficientLayerRangesPr {
                recipe_first: recipe_first as u32,
                r0_len: r0_len as u32,
                continuation_len: continuation_len as u32,
                r0_immediates,
                continuation_immediates,
            });
        }
        tables.assert_consistent();
        tables
    }

    fn push_literals(&mut self) {
        for literal in [CoefficientRecipeId::ONE, CoefficientRecipeId::NEG_ONE] {
            let value = literal
                .literal::<PR>()
                .expect("Proth120 reserved coefficient literal");
            self.push_monomials(&[(value, CoeffMonomialPr::default())]);
        }
    }

    fn push_recipe(
        &mut self,
        recipe: &NormalizedCoefficientRecipe,
        index: usize,
        top_bits: &[u32],
        _layer: usize,
        keep_zeros: bool,
    ) {
        let translated = translate_recipe(recipe, index, top_bits, keep_zeros);
        self.push_monomials(&translated);
    }

    pub(crate) fn push_monomials(&mut self, monomials: &[(PR, CoeffMonomialPr)]) {
        let offset = u32::try_from(self.monomials.len())
            .expect("Proth120 coefficient monomial table exceeds u32");

        for (coeff, monomial) in monomials {
            self.monomial_coeffs.push(*coeff);
            self.monomials.push(*monomial);
        }
        self.recipes.push(CoeffRecipePr {
            monomial_offset: offset,
            monomial_count: monomials.len() as u32,
        });
    }

    fn push_immediates(&mut self, immediates: &[u128]) -> Range<u32> {
        let start = self.immediates.len() as u32;
        self.immediates.extend(
            immediates
                .iter()
                .map(|&value| PR::from_u128_with_reduction(value)),
        );
        start..self.immediates.len() as u32
    }

    pub(crate) fn assert_consistent(&self) {
        assert_eq!(self.monomials.len(), self.monomial_coeffs.len());
        let mut next = 0u32;
        for (index, recipe) in self.recipes.iter().enumerate() {
            assert_eq!(
                recipe.monomial_offset, next,
                "Proth120 coefficient recipe {index} is not contiguous"
            );
            next += recipe.monomial_count;
        }
        assert_eq!(next as usize, self.monomials.len());
        for monomial in &self.monomials {
            for index in [monomial.challenge_idx_0, monomial.challenge_idx_1] {
                assert!(
                    index == PR_COEFF_CHALLENGE_ABSENT || usize::from(index) < PR_COEFF_CHALLENGES,
                    "Proth120 coefficient monomial names challenge slot {index}"
                );
            }
        }
        let mut recipe_next = 0u32;
        for (layer, ranges) in self.layers.iter().enumerate() {
            assert_eq!(
                ranges.recipe_first, recipe_next,
                "Proth120 coefficient layer {layer} is not contiguous"
            );
            assert!(ranges.r0_immediates.end as usize <= self.immediates.len());
            assert!(ranges.continuation_immediates.end as usize <= self.immediates.len());
            recipe_next += ranges.len();
        }
        assert_eq!(recipe_next as usize, self.recipes.len());
    }

    fn values(&self) -> Vec<PR> {
        let mut values = Vec::with_capacity(self.monomial_coeffs.len() + self.immediates.len());
        values.extend_from_slice(&self.monomial_coeffs);
        values.extend_from_slice(&self.immediates);
        values
    }

    fn index_words(&self) -> Vec<u32> {
        let mut words = Vec::with_capacity(
            self.recipes.len() * PR_COEFF_RECIPE_WORDS
                + self.monomials.len() * PR_COEFF_MONOMIAL_WORDS,
        );
        for recipe in &self.recipes {
            words.extend_from_slice(&recipe.words());
        }
        for monomial in &self.monomials {
            words.extend_from_slice(&monomial.words());
        }
        words
    }
}

pub(crate) struct CoefficientTablesPr {
    values: DeviceAllocation<PR>,
    index: DeviceAllocation<u32>,
    recipe_count: usize,
    immediate_base: usize,
    layers: Vec<CoefficientLayerRangesPr>,
}

type CoefficientWordsPr = (Vec<PR>, Vec<u32>);

fn allocate_coefficient_tables_pr(
    host: &CoefficientTablesHostPr,
    context: &ProverContext,
) -> CudaResult<(CoefficientTablesPr, CoefficientWordsPr)> {
    host.assert_consistent();
    let values_host = host.values();
    let index_host = host.index_words();
    let values = context.alloc(values_host.len(), AllocationPlacement::BestFit)?;
    let index = context.alloc(index_host.len(), AllocationPlacement::BestFit)?;

    let tables = CoefficientTablesPr {
        values,
        index,
        recipe_count: host.recipes.len(),
        immediate_base: host.monomial_coeffs.len(),
        layers: host.layers.clone(),
    };
    Ok((tables, (values_host, index_host)))
}

fn stage_coefficient_tables_pr(
    tables: &mut CoefficientTablesPr,
    (values, index): &CoefficientWordsPr,
    transfer: &mut Transfer<'_>,
) {
    transfer.stage(values, &mut tables.values);
    transfer.stage(index, &mut tables.index);
}

#[cfg(test)]
pub(crate) fn schedule_coefficient_tables_upload_pr(
    host: &CoefficientTablesHostPr,
    context: &ProverContext,
) -> CudaResult<(CoefficientTablesPr, TransferKeepalive<'static>)> {
    let (mut tables, words) = allocate_coefficient_tables_pr(host, context)?;
    let mut transfer = Transfer::new()?;
    transfer.record_allocated(context)?;
    stage_coefficient_tables_pr(&mut tables, &words, &mut transfer);
    transfer.record_transferred(context)?;
    transfer.ensure_transferred(context)?;
    Ok((tables, transfer.into_keepalive()))
}

/// Coefficient tables built and allocated before `schedule_gkr`; the caller
/// stages them into its own input transfer.
pub struct PreparedCoefficientTablesPr {
    programs: Arc<GkrProgramsPr>,
    top_bits: Vec<u32>,
    tables: CoefficientTablesPr,
    words: Option<CoefficientWordsPr>,
}

impl PreparedCoefficientTablesPr {
    pub fn new(
        programs: &Arc<GkrProgramsPr>,
        top_bits: &[u32],
        context: &ProverContext,
    ) -> CudaResult<Self> {
        let host = CoefficientTablesHostPr::build(programs, top_bits);
        let (tables, words) = allocate_coefficient_tables_pr(&host, context)?;
        Ok(Self {
            programs: Arc::clone(programs),
            top_bits: top_bits.to_vec(),
            tables,
            words: Some(words),
        })
    }

    pub fn stage_transfer(&mut self, transfer: &mut Transfer<'_>) {
        let words = self
            .words
            .take()
            .expect("Proth120 coefficient tables are staged once");
        stage_coefficient_tables_pr(&mut self.tables, &words, transfer);
    }

    pub(crate) fn into_tables(
        self,
        programs: &Arc<GkrProgramsPr>,
        top_bits: &[u32],
    ) -> CoefficientTablesPr {
        assert!(
            self.words.is_none(),
            "Proth120 coefficient tables were not staged"
        );
        assert!(
            Arc::ptr_eq(&self.programs, programs),
            "Proth120 coefficient tables were built for other programs"
        );
        assert_eq!(
            self.top_bits, top_bits,
            "Proth120 coefficient tables were built for other top bits"
        );
        self.tables
    }
}

/// Upper bound of the bytes [`PreparedCoefficientTablesPr`] stages for any top
/// bits: the tables without dropping the monomials whose coefficient is zero.
pub fn max_coefficient_table_bytes(programs: &GkrProgramsPr) -> usize {
    let top_bits = vec![1; programs.runtime_circuit.memory_layout.teardown_sets.len()];
    let host = CoefficientTablesHostPr::build_with(programs, &top_bits, true);
    host.values().len() * size_of::<PR>() + host.index_words().len() * size_of::<u32>()
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct CoefficientBankViewPr {
    pub coefficients: *const PR,
    pub coefficient_count: usize,
    pub immediates: *const PR,
    pub immediate_count: usize,
}

impl CoefficientTablesPr {
    #[cfg(test)]
    pub(crate) fn layers(&self) -> &[CoefficientLayerRangesPr] {
        &self.layers
    }

    fn immediates(&self, range: &Range<u32>) -> (*const PR, usize) {
        let count = (range.end - range.start) as usize;
        if count == 0 {
            return (std::ptr::null(), 0);
        }
        let start = self.immediate_base + range.start as usize;
        assert!(start + count <= self.values.len());
        (unsafe { self.values.as_ptr().add(start) }, count)
    }
}

pub(crate) struct CoefficientBankPr {
    values: DeviceAllocation<PR>,
    layer: usize,
    r0_len: usize,
    r0_immediates: (*const PR, usize),
    continuation_immediates: (*const PR, usize),
}

impl CoefficientBankPr {
    pub(crate) fn new(
        tables: &CoefficientTablesPr,
        layer: usize,
        context: &ProverContext,
    ) -> CudaResult<Self> {
        let ranges = tables
            .layers
            .get(layer)
            .unwrap_or_else(|| panic!("Proth120 coefficient bank layer {layer} is absent"));
        let values = context.alloc(ranges.len() as usize, AllocationPlacement::BestFit)?;

        Ok(Self {
            values,
            layer,
            r0_len: ranges.r0_len as usize,
            r0_immediates: tables.immediates(&ranges.r0_immediates),
            continuation_immediates: tables.immediates(&ranges.continuation_immediates),
        })
    }

    #[cfg(test)]
    pub(crate) fn values(&self) -> *const PR {
        self.values.as_ptr()
    }

    #[cfg(test)]
    pub(crate) fn len(&self) -> usize {
        self.values.len()
    }

    pub(crate) fn r0(&self) -> CoefficientBankViewPr {
        CoefficientBankViewPr {
            coefficients: self.values.as_ptr(),
            coefficient_count: self.r0_len,
            immediates: self.r0_immediates.0,
            immediate_count: self.r0_immediates.1,
        }
    }

    pub(crate) fn continuation(&self) -> CoefficientBankViewPr {
        CoefficientBankViewPr {
            coefficients: unsafe { self.values.as_ptr().add(self.r0_len) },
            coefficient_count: self.values.len() - self.r0_len,
            immediates: self.continuation_immediates.0,
            immediate_count: self.continuation_immediates.1,
        }
    }

    pub(crate) fn main_tail(&self) -> CoefficientBankViewPr {
        self.continuation()
    }
}

pub(crate) fn schedule_coefficient_bank_fill_pr(
    tables: &CoefficientTablesPr,
    bank: &mut CoefficientBankPr,
    challenges: *const PR,
    claim_batching: *const PR,
    context: &ProverContext,
) -> CudaResult<()> {
    let ranges = &tables.layers[bank.layer];
    assert_eq!(ranges.len() as usize, bank.values.len());
    schedule_coefficient_range_fill_pr(
        tables,
        ranges.recipe_first,
        ranges.len(),
        challenges,
        claim_batching,
        bank.values.as_mut_ptr(),
        context,
    )
}

pub(crate) fn schedule_coefficient_range_fill_pr(
    tables: &CoefficientTablesPr,
    recipe_first: u32,
    count: u32,
    challenges: *const PR,
    claim_batching: *const PR,
    coefficients: *mut PR,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(
        !challenges.is_null() && !claim_batching.is_null() && !coefficients.is_null(),
        "Proth120 coefficient fill needs device pointers"
    );
    assert!(count > 0, "Proth120 coefficient fill range is empty");
    assert!(
        recipe_first as usize + count as usize <= tables.recipe_count,
        "Proth120 coefficient fill range exceeds the recipe table"
    );
    let monomials = unsafe {
        tables
            .index
            .as_ptr()
            .add(tables.recipe_count * PR_COEFF_RECIPE_WORDS)
    };
    let desc = CoeffFillDescPr {
        recipes: tables.index.as_ptr().cast(),
        monomials: monomials.cast(),
        monomial_coeffs: tables.values.as_ptr(),
        challenges,
        claim_batching,
        coefficients,
        recipe_first,
        recipe_count: count,
    };
    let config = CudaLaunchConfig::basic(
        count.div_ceil(PR_COEFF_FILL_WARPS),
        PR_COEFF_FILL_BLOCK_THREADS,
        context.get_exec_stream(),
    );
    PrEvalCoefficientsFunction::default().launch(&config, &PrEvalCoefficientsArguments::new(desc))
}
