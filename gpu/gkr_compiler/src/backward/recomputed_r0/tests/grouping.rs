//! Decode regrouped terms independently of the compiler's grouping/emission routines.
use super::super::*;
use super::Bf;
use crate::backward::CoeffProduct;
use field::{Field, PrimeField};
use std::collections::HashMap;
const GROUP_BF: u16 = 6;
const GROUP_E4: u16 = 7;
const NEG_ONE: u32 = 2_013_265_920;
fn scale(recipe: &NormalizedCoefficientRecipe, s: u32) -> NormalizedCoefficientRecipe {
    let scale = Bf::from_u32_with_reduction(s);
    NormalizedCoefficientRecipe::from_terms(
        recipe
            .terms
            .iter()
            .map(|t| {
                let mut v = Bf::from_u32_with_reduction(t.scalar);
                v.mul_assign(&scale);
                CoeffProduct {
                    scalar: v.as_u32_reduced(),
                    challenges: t.challenges.clone(),
                    inits_and_teardowns_top_bits: t.inits_and_teardowns_top_bits.clone(),
                }
            })
            .collect(),
    )
}
fn key(r: &NormalizedCoefficientRecipe) -> String {
    format!("{:?}", r.terms)
}

struct Decoder<'a> {
    p: &'a WindowProgram,
    lanes: HashMap<u32, u16>,
}
impl<'a> Decoder<'a> {
    fn new(p: &'a WindowProgram) -> Self {
        Decoder {
            p,
            lanes: p.source_lanes.iter().map(|l| (l.word, l.source)).collect(),
        }
    }
    fn rec(&self, pc: usize) -> (u16, u16, u16, u16) {
        let w = &self.p.words;
        (w[4 * pc], w[4 * pc + 1], w[4 * pc + 2], w[4 * pc + 3])
    }
    fn operand(&self, pc: usize, which: usize) -> String {
        let idx = (4 * pc + which) as u32;
        match self.lanes.get(&idx) {
            Some(s) => format!("S{s}"),
            None => format!("W{}", self.p.words[idx as usize]),
        }
    }
    fn plan(&self, id: u16) -> NormalizedCoefficientRecipe {
        match id & 0x7fff {
            0 => NormalizedCoefficientRecipe::one(),
            1 => NormalizedCoefficientRecipe::neg_one(),
            n => match &self.p.coefficient_plans[(n - 2) as usize] {
                WindowCoefficientPlan::Direct(r) => r.clone(),
                WindowCoefficientPlan::Scaled { recipe, scalar } => scale(recipe, *scalar),
                WindowCoefficientPlan::LinearBasis { recipe, .. } => recipe.clone(),
            },
        }
    }
    fn signed_plan(&self, factor: u16) -> NormalizedCoefficientRecipe {
        let r = self.plan(factor);
        if factor & 0x8000 != 0 {
            scale(&r, NEG_ONE)
        } else {
            r
        }
    }
    fn immediate(&self, factor: u16) -> u32 {
        match factor & 0x7fff {
            0 => 1,
            1 => NEG_ONE,
            n => Bf::from_raw_u32(self.p.immediates[(n - 2) as usize]).as_u32_reduced(),
        }
    }
    /// One entry per evaluated term across all four sections.
    fn entries(&self) -> Vec<String> {
        let s = &self.p.sections;
        let mut out = Vec::new();
        let mut pc = 0usize;
        while pc < s[0] as usize {
            let (op, factor, a, _b) = self.rec(pc);
            if op != GROUP_BF {
                out.push(format!(
                    "BF|{op}|{}|{}|{}",
                    self.operand(pc, 2),
                    self.operand(pc, 3),
                    key(&self.signed_plan(factor))
                ));
                pc += 1;
                continue;
            }
            let core = self.plan(factor);
            let arity = a as usize;
            let prefix = (self.rec(pc).3 & 0x7fff) as usize;
            assert_ne!(
                prefix, 1,
                "recomputed lowering emitted an unsupported single-product prefix"
            );
            assert!(prefix <= arity);
            pc += 1;
            for m in 0..arity {
                let (mop, mf, _, _) = self.rec(pc);
                if m >= prefix {
                    assert!(
                        matches!(mop, 0 | 4),
                        "tail member with product opcode {mop}"
                    );
                } else {
                    assert!(
                        matches!(mop, 2 | 8 | 9),
                        "prefix member with non-product opcode {mop}"
                    );
                }
                let eff = scale(&core, self.immediate(mf));
                out.push(format!(
                    "BF|{mop}|{}|{}|{}",
                    self.operand(pc, 2),
                    self.operand(pc, 3),
                    key(&eff)
                ));
                pc += 1;
            }
        }
        while pc < s[1] as usize {
            let (op, factor, _, _) = self.rec(pc);
            out.push(format!(
                "LE4|{op}|{}|{}",
                self.operand(pc, 2),
                key(&self.plan(factor))
            ));
            pc += 1;
        }
        while pc < s[2] as usize {
            let (op, factor, _, _) = self.rec(pc);
            out.push(format!(
                "SE4|{op}|{}|{}|{}",
                self.operand(pc, 2),
                self.operand(pc, 3),
                key(&self.signed_plan(factor))
            ));
            pc += 1;
        }
        while pc < s[3] as usize {
            let (op, factor, _, _) = self.rec(pc);
            assert_eq!(op, GROUP_E4);
            let core = self.plan(factor);
            pc += 1;
            for _ in 0..2 {
                let (mop, mf, _, _) = self.rec(pc);
                out.push(format!(
                    "PE4|{mop}|{}|{}|{}",
                    self.operand(pc, 2),
                    self.operand(pc, 3),
                    key(&scale(&core, self.immediate(mf)))
                ));
                pc += 1;
            }
        }
        assert_eq!(pc, s[3] as usize);
        out.sort();
        out
    }
}

#[test]
fn cpu_linear_tails_preserve_terms_and_seed_corpus() {
    let mut layers = 0;
    let mut expected_layers = 0;
    for name in crate::backward::corpus_tests::CORPUS {
        let dag = super::load_dag(name);
        expected_layers += 1 * dag.layers.len();
        let originals = compile_recomputed_r0(&dag, false).unwrap();
        let grouped = compile_recomputed_r0(&dag, true).unwrap();
        assert_eq!(originals.len(), grouped.len());
        for (a, b) in originals.iter().zip(&grouped) {
            let da = Decoder::new(&a.window);
            let db = Decoder::new(&b.window);
            assert_eq!(a.window.windows, b.window.windows, "{name} L{}", a.layer);
            assert_eq!(
                a.window.source_slots, b.window.source_slots,
                "{name} L{}",
                a.layer
            );
            assert_eq!(da.entries(), db.entries(), "{name} L{}", a.layer);
            assert_eq!(
                a.scalar_seed.map(|s| da.plan(s)),
                b.scalar_seed.map(|s| db.plan(s)),
                "{name} L{} scalar seed changed",
                a.layer
            );
            // The window seed is the coefficient layer's constant term, in both lowerings.
            assert_eq!(a.coefficients, b.coefficients, "{name} L{}", a.layer);
            let c_init = c_init_recipe(&a.coefficients);
            assert_eq!(
                a.scalar_seed.map(|s| da.plan(s)),
                c_init,
                "{name} L{} original seed is not c_init",
                a.layer
            );
            assert_eq!(
                b.scalar_seed.map(|s| db.plan(s)),
                c_init,
                "{name} L{} grouped seed is not c_init",
                a.layer
            );
            assert_eq!(a.window.shape.bits() & !0x7f7, 0);
            assert_eq!(b.window.shape.bits() & !0x7ff, 0);
            assert!(a.window.words.len() <= 8192 && b.window.words.len() <= 8192);
            layers += 1;
        }
    }
    assert!(expected_layers > 0);
    assert_eq!(layers, expected_layers);
}
