use std::collections::BTreeMap;

use cs::definitions::NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES;
use field::{Field, PrimeField};

use crate::primitives::field::BF;

pub(crate) const IMMEDIATE_FACTOR_ABSENT: u8 = 0xff;
pub(crate) const IMMEDIATE_FACTOR_ADDITIVE_PART_IDX: u8 =
    NUM_PERMUTATION_ARGUMENT_LINEARIZATION_CHALLENGES as u8;

/// CUDA mirror: `immediate_factor_recipe_header`.
#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct ImmediateFactorRecipeHeader {
    pub monomial_offset: u16,
    pub monomial_count: u8,
    pub _pad: u8,
}

impl Default for ImmediateFactorRecipeHeader {
    fn default() -> Self {
        Self {
            monomial_offset: 0,
            monomial_count: 0,
            _pad: 0,
        }
    }
}

/// CUDA mirror: `immediate_factor_monomial`.
#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct ImmediateFactorMonomial {
    pub coeff: BF,
    pub challenge_idx_0: u8,
    pub challenge_idx_1: u8,
    pub power_0: u8,
    pub power_1: u8,
}

impl Default for ImmediateFactorMonomial {
    fn default() -> Self {
        Self {
            coeff: BF::ZERO,
            challenge_idx_0: IMMEDIATE_FACTOR_ABSENT,
            challenge_idx_1: IMMEDIATE_FACTOR_ABSENT,
            power_0: 0,
            power_1: 0,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ImmediateFactorRecipeStructural {
    monomials: Vec<ImmediateFactorMonomial>,
}

impl ImmediateFactorRecipeStructural {
    pub fn zero() -> Self {
        Self {
            monomials: Vec::new(),
        }
    }

    pub fn one() -> Self {
        Self::from_base(BF::ONE)
    }

    pub fn from_base(coeff: BF) -> Self {
        if coeff.is_zero() {
            Self::zero()
        } else {
            Self {
                monomials: vec![ImmediateFactorMonomial {
                    coeff,
                    challenge_idx_0: IMMEDIATE_FACTOR_ABSENT,
                    challenge_idx_1: IMMEDIATE_FACTOR_ABSENT,
                    power_0: 0,
                    power_1: 0,
                }],
            }
        }
    }

    pub fn challenge(idx: u8) -> Self {
        Self::challenge_scaled(idx, BF::ONE)
    }

    pub fn challenge_scaled(idx: u8, coeff: BF) -> Self {
        if coeff.is_zero() {
            Self::zero()
        } else {
            Self {
                monomials: vec![ImmediateFactorMonomial {
                    coeff,
                    challenge_idx_0: idx,
                    challenge_idx_1: IMMEDIATE_FACTOR_ABSENT,
                    power_0: 1,
                    power_1: 0,
                }],
            }
        }
    }

    pub fn add(&self, other: &Self) -> Self {
        let mut monomials = Vec::with_capacity(self.monomials.len() + other.monomials.len());
        monomials.extend_from_slice(&self.monomials);
        monomials.extend_from_slice(&other.monomials);
        Self { monomials }.normalized()
    }

    pub fn mul(&self, other: &Self) -> Self {
        if self.monomials.is_empty() || other.monomials.is_empty() {
            return Self::zero();
        }
        let mut monomials = Vec::with_capacity(self.monomials.len() * other.monomials.len());
        for lhs in &self.monomials {
            for rhs in &other.monomials {
                monomials.push(mul_monomials(lhs, rhs));
            }
        }
        Self { monomials }.normalized()
    }

    pub fn negated(&self) -> Self {
        let mut result = self.clone();
        for monomial in &mut result.monomials {
            monomial.coeff.negate();
        }
        result
    }

    pub fn monomials(&self) -> &[ImmediateFactorMonomial] {
        &self.monomials
    }

    pub fn key(&self) -> Vec<(u32, u8, u8, u8, u8)> {
        self.monomials
            .iter()
            .map(|m| {
                (
                    m.coeff.as_u32_raw_repr_reduced(),
                    m.challenge_idx_0,
                    m.challenge_idx_1,
                    m.power_0,
                    m.power_1,
                )
            })
            .collect()
    }

    fn normalized(self) -> Self {
        let mut by_factors: BTreeMap<(u8, u8, u8, u8), BF> = BTreeMap::new();
        for monomial in self.monomials {
            if monomial.coeff.is_zero() {
                continue;
            }
            let key = (
                monomial.challenge_idx_0,
                monomial.challenge_idx_1,
                monomial.power_0,
                monomial.power_1,
            );
            by_factors
                .entry(key)
                .and_modify(|coeff| {
                    coeff.add_assign(&monomial.coeff);
                })
                .or_insert(monomial.coeff);
        }
        let monomials = by_factors
            .into_iter()
            .filter_map(
                |((challenge_idx_0, challenge_idx_1, power_0, power_1), coeff)| {
                    if coeff.is_zero() {
                        None
                    } else {
                        Some(ImmediateFactorMonomial {
                            coeff,
                            challenge_idx_0,
                            challenge_idx_1,
                            power_0,
                            power_1,
                        })
                    }
                },
            )
            .collect();
        Self { monomials }
    }
}

impl Default for ImmediateFactorRecipeStructural {
    fn default() -> Self {
        Self::one()
    }
}

#[derive(Default)]
pub(crate) struct ImmediateFactorInterner {
    keys: BTreeMap<Vec<(u32, u8, u8, u8, u8)>, u16>,
    recipes: Vec<ImmediateFactorRecipeStructural>,
}

impl ImmediateFactorInterner {
    pub fn new() -> Self {
        let mut interner = Self::default();
        let one = ImmediateFactorRecipeStructural::one();
        interner.keys.insert(one.key(), 0);
        interner.recipes.push(one);
        interner
    }

    pub fn intern(&mut self, recipe: ImmediateFactorRecipeStructural) -> u16 {
        let key = recipe.key();
        if let Some(idx) = self.keys.get(&key).copied() {
            return idx;
        }
        let idx = self.recipes.len();
        assert!(
            idx <= u16::MAX as usize,
            "too many immediate factor recipes"
        );
        let idx = idx as u16;
        self.keys.insert(key, idx);
        self.recipes.push(recipe);
        idx
    }

    pub fn materialize(
        &self,
    ) -> (
        Vec<ImmediateFactorRecipeHeader>,
        Vec<ImmediateFactorMonomial>,
    ) {
        let mut headers = Vec::with_capacity(self.recipes.len());
        let mut monomials = Vec::new();
        for recipe in &self.recipes {
            let offset = monomials.len();
            assert!(
                offset <= u16::MAX as usize,
                "too many immediate factor monomials"
            );
            assert!(
                recipe.monomials().len() <= u8::MAX as usize,
                "too many monomials in one immediate factor recipe"
            );
            headers.push(ImmediateFactorRecipeHeader {
                monomial_offset: offset as u16,
                monomial_count: recipe.monomials().len() as u8,
                _pad: 0,
            });
            monomials.extend_from_slice(recipe.monomials());
        }
        (headers, monomials)
    }
}

fn mul_monomials(
    lhs: &ImmediateFactorMonomial,
    rhs: &ImmediateFactorMonomial,
) -> ImmediateFactorMonomial {
    let mut coeff = lhs.coeff;
    coeff.mul_assign(&rhs.coeff);

    let mut factors: BTreeMap<u8, u16> = BTreeMap::new();
    for (idx, power) in [
        (lhs.challenge_idx_0, lhs.power_0),
        (lhs.challenge_idx_1, lhs.power_1),
        (rhs.challenge_idx_0, rhs.power_0),
        (rhs.challenge_idx_1, rhs.power_1),
    ] {
        if idx == IMMEDIATE_FACTOR_ABSENT || power == 0 {
            continue;
        }
        *factors.entry(idx).or_default() += power as u16;
    }
    assert!(
        factors.len() <= 2,
        "immediate factor monomial product exceeded two distinct challenge factors"
    );
    let mut it = factors.into_iter();
    let (challenge_idx_0, power_0) = it
        .next()
        .map(|(idx, power)| {
            assert!(power <= u8::MAX as u16, "immediate factor power overflow");
            (idx, power as u8)
        })
        .unwrap_or((IMMEDIATE_FACTOR_ABSENT, 0));
    let (challenge_idx_1, power_1) = it
        .next()
        .map(|(idx, power)| {
            assert!(power <= u8::MAX as u16, "immediate factor power overflow");
            (idx, power as u8)
        })
        .unwrap_or((IMMEDIATE_FACTOR_ABSENT, 0));

    ImmediateFactorMonomial {
        coeff,
        challenge_idx_0,
        challenge_idx_1,
        power_0,
        power_1,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use field::FieldExtension;

    use crate::primitives::field::E4;

    impl ImmediateFactorRecipeStructural {
        pub fn evaluate(&self, ext_challenges: &[E4]) -> E4 {
            let mut acc = E4::ZERO;
            for monomial in &self.monomials {
                let mut term = E4::from_base(monomial.coeff);
                if monomial.challenge_idx_0 != IMMEDIATE_FACTOR_ABSENT {
                    term.mul_assign(
                        &ext_challenges[monomial.challenge_idx_0 as usize]
                            .pow(monomial.power_0 as u32),
                    );
                }
                if monomial.challenge_idx_1 != IMMEDIATE_FACTOR_ABSENT {
                    term.mul_assign(
                        &ext_challenges[monomial.challenge_idx_1 as usize]
                            .pow(monomial.power_1 as u32),
                    );
                }
                acc.add_assign(&term);
            }
            acc
        }
    }

    fn sample_ext(seed: u32) -> E4 {
        E4::from_array_of_base([
            BF::from_u64_with_reduction(seed as u64),
            BF::from_u64_with_reduction(seed as u64 + 1),
            BF::from_u64_with_reduction(seed as u64 + 2),
            BF::from_u64_with_reduction(seed as u64 + 3),
        ])
    }

    #[test]
    fn structural_evaluation_matches_pre_evaluated_path() {
        let challenges = (0..7).map(|i| sample_ext(10 + i)).collect::<Vec<_>>();
        let recipe = ImmediateFactorRecipeStructural::challenge_scaled(0, BF::new(3))
            .add(&ImmediateFactorRecipeStructural::challenge_scaled(
                6,
                BF::new(5),
            ))
            .mul(&ImmediateFactorRecipeStructural::challenge_scaled(
                2,
                BF::new(7),
            ))
            .negated();

        let mut expected = challenges[0];
        expected.mul_assign_by_base(&BF::new(3));
        let mut additive = challenges[6];
        additive.mul_assign_by_base(&BF::new(5));
        expected.add_assign(&additive);
        let mut tail = challenges[2];
        tail.mul_assign_by_base(&BF::new(7));
        expected.mul_assign(&tail);
        expected.negate();

        assert_eq!(recipe.evaluate(&challenges), expected);
    }

    #[test]
    fn structural_interner_deduplicates_one_at_slot_zero() {
        let mut interner = ImmediateFactorInterner::new();
        assert_eq!(interner.intern(ImmediateFactorRecipeStructural::one()), 0);
        let idx = interner.intern(ImmediateFactorRecipeStructural::challenge(3));
        assert_ne!(idx, 0);
        assert_eq!(
            interner.intern(ImmediateFactorRecipeStructural::challenge(3)),
            idx
        );
    }
}
