use std::ffi::c_void;
use std::mem::{align_of, offset_of, size_of};

use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart_sys::{cudaGetSymbolAddress, cuda_struct_and_stub};
use gpu_gkr_compiler::{CoefficientRecipeId, NormalizedCoefficientRecipe, WindowCoefficientPlan};
use gpu_prover_context::ProverContext;

use crate::backward::coefficient_chunks::coefficient_chunk_ranges;
use crate::backward::window::coefficient_bank::{
    translate_coefficient_recipe, BWD_COEFF_CHALLENGE_CLAIM_BATCHING,
    BWD_COEFF_CHALLENGE_LOOKUP_ADDITIVE,
};
use crate::proth120::programs::GkrProgramsPr;
use crate::upstream::{Field, PR};

pub(crate) const PR_COEFF_CHALLENGES: usize = 9;
pub(crate) const PR_COEFF_CHALLENGE_ABSENT: u8 =
    crate::backward::window::coefficient_bank::BWD_COEFF_CHALLENGE_ABSENT;
const PR_COEFF_CHUNK_RECIPES: usize = 278;
const PR_COEFF_CHUNK_MONOMIALS: usize = 577;
const PR_COEFF_CHUNK_IMMEDIATES: usize = 17;
const PR_COEFF_BANK_STRIDE: usize = PR_COEFF_CHUNK_RECIPES + PR_COEFF_CHUNK_IMMEDIATES;
const PR_COEFF_BANK_CAPACITY: usize = 2 * PR_COEFF_BANK_STRIDE;
const _: () = assert!(PR_COEFF_BANK_CAPACITY * size_of::<PR>() == 9440);
cuda_struct_and_stub! { static ab_pr_gkr_bwd_coeff_bank: [PR; PR_COEFF_BANK_CAPACITY]; }
pub(crate) fn coefficient_bank_device_ptr_pr() -> CudaResult<*mut PR> {
    let mut pointer: *mut c_void = std::ptr::null_mut();
    // SAFETY: this Rust stub names the matching CUDA constant symbol in gpu_gkr_native.
    unsafe {
        cudaGetSymbolAddress(
            &mut pointer,
            &ab_pr_gkr_bwd_coeff_bank as *const _ as *const c_void,
        )
    }
    .wrap()?;
    Ok(pointer.cast())
}
const PR_COEFF_FILL_BLOCK_THREADS: u32 = 128;
const PR_COEFF_FILL_WARPS: u32 = 4;
const PR_COEFF_ARGUMENT_LIMIT: usize = 32764;
pub(crate) const PR_EVAL_COEFFICIENTS_ARGUMENT_BYTES: usize =
    size_of::<CoeffChunkDescPr>() + 3 * size_of::<*const PR>();

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
}

#[repr(C)]
#[derive(Clone)]
pub(crate) struct CoeffChunkDescPr {
    pub bank_first: u32,
    pub bank_count: u32,
    pub monomial_count: u32,
    pub immediate_count: u32,
    pub recipes: [CoeffRecipePr; PR_COEFF_CHUNK_RECIPES],
    pub monomials: [CoeffMonomialPr; PR_COEFF_CHUNK_MONOMIALS],
    pub monomial_coeffs: [PR; PR_COEFF_CHUNK_MONOMIALS],
    pub immediates: [PR; PR_COEFF_CHUNK_IMMEDIATES],
}

impl Default for CoeffChunkDescPr {
    fn default() -> Self {
        Self {
            bank_first: 0,
            bank_count: 0,
            monomial_count: 0,
            immediate_count: 0,
            recipes: [CoeffRecipePr::default(); PR_COEFF_CHUNK_RECIPES],
            monomials: [CoeffMonomialPr::default(); PR_COEFF_CHUNK_MONOMIALS],
            monomial_coeffs: [PR::ZERO; PR_COEFF_CHUNK_MONOMIALS],
            immediates: [PR::ZERO; PR_COEFF_CHUNK_IMMEDIATES],
        }
    }
}

const _: () = {
    assert!(size_of::<PR>() == 16 && align_of::<PR>() == 16);
    assert!(size_of::<CoeffRecipePr>() == 8 && align_of::<CoeffRecipePr>() == 4);
    assert!(offset_of!(CoeffRecipePr, monomial_offset) == 0);
    assert!(offset_of!(CoeffRecipePr, monomial_count) == 4);
    assert!(size_of::<CoeffMonomialPr>() == 8 && align_of::<CoeffMonomialPr>() == 2);
    assert!(offset_of!(CoeffMonomialPr, challenge_idx_0) == 2);
    assert!(offset_of!(CoeffMonomialPr, challenge_idx_1) == 3);
    assert!(offset_of!(CoeffMonomialPr, power_0) == 4);
    assert!(offset_of!(CoeffMonomialPr, power_1) == 5);
    assert!(size_of::<CoeffChunkDescPr>() == 16368 && align_of::<CoeffChunkDescPr>() == 16);
    assert!(offset_of!(CoeffChunkDescPr, recipes) == 16);
    assert!(offset_of!(CoeffChunkDescPr, monomials) == 2240);
    assert!(offset_of!(CoeffChunkDescPr, monomial_coeffs) == 6864);
    assert!(offset_of!(CoeffChunkDescPr, immediates) == 16096);
    assert!(PR_EVAL_COEFFICIENTS_ARGUMENT_BYTES == 16392);
    assert!(PR_EVAL_COEFFICIENTS_ARGUMENT_BYTES <= PR_COEFF_ARGUMENT_LIMIT);
    assert!(BWD_COEFF_CHALLENGE_CLAIM_BATCHING as usize == PR_COEFF_CHALLENGES);
    // Lookup additive is the highest non-batching slot in the shared layout.
    assert!((BWD_COEFF_CHALLENGE_LOOKUP_ADDITIVE as usize) < PR_COEFF_CHALLENGES);
};

cuda_kernel!(PrEvalCoefficients, ab_pr_gkr_bwd_eval_coefficients_kernel(
    desc: CoeffChunkDescPr, challenges: *const PR, claim_batching: *const PR, coefficients: *mut PR
));

/// One bank, normalized with this proof's top bits before building by-value chunks.
#[derive(Clone, Debug, Default)]
pub(crate) struct CoefficientBankHostPr {
    pub recipes: Vec<CoeffRecipePr>,
    pub monomials: Vec<CoeffMonomialPr>,
    pub monomial_coeffs: Vec<PR>,
    pub immediates: Vec<PR>,
}

fn translate_recipe(
    recipe: &NormalizedCoefficientRecipe,
    recipe_index: usize,
    top_bits: &[u32],
) -> Vec<(PR, CoeffMonomialPr)> {
    translate_coefficient_recipe(recipe, recipe_index, top_bits, PR::from_u128_with_reduction)
        .unwrap_or_else(|error| panic!("Proth120 coefficient binding: {error:?}"))
        .map(|(scalar, key)| (scalar, CoeffMonomialPr::from_key(key)))
        .collect()
}

impl CoefficientBankHostPr {
    pub(crate) fn build(
        programs: &GkrProgramsPr,
        layer: usize,
        top_bits: &[u32],
        r0: bool,
    ) -> Self {
        let window = &programs.r0[layer].window;
        let continuation = &programs.continuations.layers[layer].coefficients;
        assert_eq!(
            continuation.immediates,
            programs.main_continuation_window[layer].immediates
        );
        assert_eq!(
            continuation.immediates,
            programs.main_tail[layer].immediates
        );
        let mut bank = Self::default();
        for literal in [CoefficientRecipeId::ONE, CoefficientRecipeId::NEG_ONE] {
            bank.push_monomials(&[(
                literal
                    .literal::<PR>()
                    .expect("reserved coefficient literal"),
                CoeffMonomialPr::default(),
            )]);
        }
        if r0 {
            for (index, plan) in window.coefficient_plans.iter().enumerate() {
                let WindowCoefficientPlan::Direct(recipe) = plan else {
                    panic!("Proth120 R0 layer {layer} plan {index} must be Direct");
                };
                bank.push_monomials(&translate_recipe(recipe, index, top_bits));
            }
        } else {
            for (index, recipe) in continuation.coefficients.iter().enumerate() {
                bank.push_monomials(&translate_recipe(recipe, index, top_bits));
            }
        }
        bank.immediates = if r0 {
            &window.immediates
        } else {
            &continuation.immediates
        }
        .iter()
        .map(|&value| PR::from_u128_with_reduction(value))
        .collect();
        bank
    }

    fn push_monomials(&mut self, monomials: &[(PR, CoeffMonomialPr)]) {
        let offset =
            u32::try_from(self.monomials.len()).expect("coefficient monomial offset fits u32");
        self.recipes.push(CoeffRecipePr {
            monomial_offset: offset,
            monomial_count: monomials.len() as u32,
        });
        for (coeff, monomial) in monomials {
            self.monomial_coeffs.push(*coeff);
            self.monomials.push(*monomial);
        }
    }

    pub(crate) fn chunks(&self) -> Vec<Box<CoeffChunkDescPr>> {
        assert_eq!(self.monomials.len(), self.monomial_coeffs.len());
        assert!(
            self.immediates.len() <= PR_COEFF_CHUNK_IMMEDIATES,
            "Proth120 immediate bank exceeds by-value capacity"
        );
        let ranges = coefficient_chunk_ranges(
            self.recipes
                .iter()
                .map(|r| (r.monomial_offset as usize, r.monomial_count as usize)),
            self.monomials.len(),
            PR_COEFF_CHUNK_RECIPES,
            PR_COEFF_CHUNK_MONOMIALS,
        );
        let last = ranges.len() - 1;
        ranges
            .into_iter()
            .enumerate()
            .map(|(index, range)| {
                let mut desc = Box::new(CoeffChunkDescPr::default());
                desc.bank_first = range.recipes.start as u32;
                desc.bank_count = range.recipes.len() as u32;
                desc.monomial_count = range.monomials.len() as u32;
                for (dst, recipe) in desc.recipes.iter_mut().zip(&self.recipes[range.recipes]) {
                    *dst = CoeffRecipePr {
                        monomial_offset: recipe.monomial_offset - range.monomials.start as u32,
                        ..*recipe
                    };
                }
                desc.monomials[..range.monomials.len()]
                    .copy_from_slice(&self.monomials[range.monomials.clone()]);
                desc.monomial_coeffs[..range.monomials.len()]
                    .copy_from_slice(&self.monomial_coeffs[range.monomials]);
                if index == last {
                    desc.immediate_count = self.immediates.len() as u32;
                    desc.immediates[..self.immediates.len()].copy_from_slice(&self.immediates);
                }
                assert!(
                    desc.bank_count > 0,
                    "Proth120 coefficient fill chunk is empty"
                );
                desc
            })
            .collect()
    }
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct CoefficientBankViewPr {
    pub coefficient_offset: u32,
    pub coefficient_count: usize,
    pub immediate_offset: u32,
    pub immediate_count: usize,
}

struct EvaluatedCoefficientBankPr {
    destination: *mut PR,
    offset: u32,
    coefficient_count: usize,
    immediate_count: usize,
    chunks: Vec<Box<CoeffChunkDescPr>>,
}

impl EvaluatedCoefficientBankPr {
    fn new(host: &CoefficientBankHostPr, offset: usize, symbol: *mut PR) -> Self {
        assert!(
            host.recipes.len() + host.immediates.len() <= PR_COEFF_BANK_STRIDE,
            "Proth120 evaluated coefficient bank exceeds its constant range"
        );
        Self {
            // SAFETY: each of the two ranges fits the fixed-size constant symbol.
            destination: unsafe { symbol.add(offset) },
            offset: offset as u32,
            coefficient_count: host.recipes.len(),
            immediate_count: host.immediates.len(),
            chunks: host.chunks(),
        }
    }

    fn view(&self) -> CoefficientBankViewPr {
        CoefficientBankViewPr {
            coefficient_offset: self.offset,
            coefficient_count: self.coefficient_count,
            immediate_offset: self.offset + self.coefficient_count as u32,
            immediate_count: self.immediate_count,
        }
    }

    fn schedule_fill(
        &mut self,
        challenges: *const PR,
        claim_batching: *const PR,
        context: &ProverContext,
    ) -> CudaResult<()> {
        for desc in &self.chunks {
            let config = CudaLaunchConfig::basic(
                desc.bank_count.div_ceil(PR_COEFF_FILL_WARPS),
                PR_COEFF_FILL_BLOCK_THREADS,
                context.get_exec_stream(),
            );
            PrEvalCoefficientsFunction::default().launch(
                &config,
                &PrEvalCoefficientsArguments::new(
                    (**desc).clone(),
                    challenges,
                    claim_batching,
                    self.destination,
                ),
            )?;
        }
        Ok(())
    }
}

/// Separate R0 and continuation banks, with no input-table allocation or transfer.
pub(crate) struct CoefficientBankPr {
    r0: EvaluatedCoefficientBankPr,
    continuation: EvaluatedCoefficientBankPr,
}

impl CoefficientBankPr {
    pub(crate) fn new(
        programs: &GkrProgramsPr,
        layer: usize,
        top_bits: &[u32],
    ) -> CudaResult<Self> {
        let symbol = coefficient_bank_device_ptr_pr()?;
        Ok(Self {
            r0: EvaluatedCoefficientBankPr::new(
                &CoefficientBankHostPr::build(programs, layer, top_bits, true),
                0,
                symbol,
            ),
            continuation: EvaluatedCoefficientBankPr::new(
                &CoefficientBankHostPr::build(programs, layer, top_bits, false),
                PR_COEFF_BANK_STRIDE,
                symbol,
            ),
        })
    }

    pub(crate) fn r0(&self) -> CoefficientBankViewPr {
        self.r0.view()
    }
    pub(crate) fn continuation(&self) -> CoefficientBankViewPr {
        self.continuation.view()
    }
    pub(crate) fn main_tail(&self) -> CoefficientBankViewPr {
        self.continuation()
    }
}

pub(crate) fn schedule_coefficient_bank_fill_pr(
    bank: &mut CoefficientBankPr,
    challenges: *const PR,
    claim_batching: *const PR,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(
        !challenges.is_null() && !claim_batching.is_null(),
        "Proth120 coefficient fill needs device challenge pointers"
    );
    bank.r0.schedule_fill(challenges, claim_batching, context)?;
    bank.continuation
        .schedule_fill(challenges, claim_batching, context)
}
