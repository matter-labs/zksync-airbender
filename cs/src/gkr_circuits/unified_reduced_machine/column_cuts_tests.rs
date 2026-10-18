use super::circuit::{
    dispatch_sum, pc_bump_gate, FAMILY_2_FLAG_OFFSET, UNIFIED_REDUCED_MACHINE_NUM_FLAGS,
};
use super::decoder::{unified_decoder_mask_violation, UnifiedReducedMachineFamilyCircuitMask};
use super::jump_branch_slt::f2_rd_write_gates;
use crate::constraint::{Constraint, Term};
use crate::definitions::Variable;
use crate::gkr_circuits::jump_branch_slt_family::{
    BRANCH_BIT, JALR_BIT, JAL_BIT, RD_IS_ZERO_BIT, SLT_BIT,
};
use crate::gkr_compiler::GKRCircuitArtifact;
use crate::structured_expr::Expr;
use crate::types::Boolean;
use crate::witness_placer::graph_description::{Expression, RawExpression};
use field::baby_bear::base::BabyBearField;
use field::{PrimeField, Proth120};
use std::collections::HashMap;

fn eval<F: PrimeField>(constraint: &Constraint<F>, values: &HashMap<Variable, F>) -> F {
    let mut result = F::ZERO;
    for term in constraint.terms.iter() {
        match term {
            Term::Constant(c) => {
                result.add_assign(c);
            }
            Term::Expression {
                coeff,
                inner,
                degree,
            } => {
                let mut t = *coeff;
                for v in &inner[..*degree] {
                    t.mul_assign(&values[v]);
                }
                result.add_assign(&t);
            }
        }
    }
    result
}

/// On every row the circuit admits (an executing row whose mask passes the check the decoder
/// table build enforces, or a padding row, whose flags are zero), the three F2 rd-write gates
/// and the PC-bump gate equal the helper columns they replace, and the dispatch tie holds.
#[test]
fn column_cut_gates_equal_the_replaced_helpers_on_admitted_rows() {
    fn check<F: PrimeField>() {
        let execute = Variable(0);
        let bits: [Variable; UNIFIED_REDUCED_MACHINE_NUM_FLAGS] =
            std::array::from_fn(|i| Variable(i as u64 + 1));
        let mask = UnifiedReducedMachineFamilyCircuitMask::from_full_mask(bits.map(Boolean::Is));
        let f2 = mask.jump_branch_slt();
        let [jj, slt, rd_zero] = f2_rd_write_gates(
            f2.perform_jal(),
            f2.perform_jalr(),
            f2.perform_slt(),
            f2.perform_branch(),
            f2.rd_is_zero(),
        );
        let gates = [
            jj,
            slt,
            rd_zero,
            pc_bump_gate(execute, &mask),
            Expr::var(execute) - dispatch_sum(&mask),
        ]
        .map(|e| e.to_max_quadratic_constraint());

        let executing: Vec<u32> = (0..1u32 << UNIFIED_REDUCED_MACHINE_NUM_FLAGS)
            .filter(|&m| unified_decoder_mask_violation(m).is_none())
            .collect();
        assert_eq!(executing.len(), 20);
        for (e, m) in executing.into_iter().map(|m| (1, m)).chain([(0, 0)]) {
            let mut values: HashMap<_, _> = bits
                .iter()
                .enumerate()
                .map(|(i, v)| (*v, F::from_u32_unchecked(m >> i & 1)))
                .collect();
            values.insert(execute, F::from_u32_unchecked(e));
            let f2_bit = |b: usize| (m >> (FAMILY_2_FLAG_OFFSET + b) & 1) as i64;
            let [j, jr, s, b, z] =
                [JAL_BIT, JALR_BIT, SLT_BIT, BRANCH_BIT, RD_IS_ZERO_BIT].map(f2_bit);
            let helpers = [
                (j + jr) * (1 - z),
                s * (1 - z),
                (j + jr + s + b) * z,
                e as i64 * (1 - (j + jr + s + b)),
                0,
            ];
            for (i, (gate, helper)) in gates.iter().zip(helpers).enumerate() {
                assert!(helper == 0 || helper == 1, "helper {i} on mask {m:#b}");
                assert_eq!(
                    eval(gate, &values),
                    F::from_u32_unchecked(helper as u32),
                    "gate {i}, execute {e}, mask {m:#b}"
                );
            }
        }
    }
    check::<BabyBearField>();
    check::<Proth120>();
}

/// The committed layouts and witness graphs of both fields: each aliased scratch slot has
/// exactly one bare RC-16 lookup, and no u8 or bool writer. The generated witness function
/// reads a masked-off target back at the writer's own width, so a narrow writer would truncate
/// the u16 limb another family leaves in the slot.
#[test]
fn aliased_slots_are_range_checked_and_written_at_least_u16() {
    fn read_json<T: serde::de::DeserializeOwned>(path: &str) -> T {
        let file = std::fs::File::open(path).unwrap_or_else(|e| panic!("{path}: {e}"));
        serde_json::from_reader(std::io::BufReader::new(file)).unwrap()
    }

    fn check<F: PrimeField + serde::de::DeserializeOwned>(layout: &str, ssa: &str) {
        let artifact: GKRCircuitArtifact<F> = read_json(layout);
        let ssa: Vec<Vec<RawExpression<F>>> = read_json(ssa);
        let slot_var = |slot: usize| {
            let name = format!("shared scratch var[{slot}]");
            let vars: Vec<Variable> = artifact
                .variable_names
                .iter()
                .filter(|(_, n)| **n == name)
                .map(|(v, _)| *v)
                .collect();
            assert_eq!(vars.len(), 1, "{layout}: {name}");
            vars[0]
        };
        let writer_types = |slot: usize| -> Vec<&'static str> {
            let var = slot_var(slot);
            ssa.iter()
                .flatten()
                .filter_map(|e| match e {
                    RawExpression::WriteVariable {
                        into_variable,
                        source_subexpr,
                        ..
                    } if *into_variable == var => Some(match source_subexpr {
                        Expression::Bool(_) => "bool",
                        Expression::Field(_) => "field",
                        Expression::U8(_) => "u8",
                        Expression::U16(_) => "u16",
                        Expression::U32(_) => "u32",
                    }),
                    _ => None,
                })
                .collect()
        };
        for slot in [17, 18, 7] {
            let addr = artifact.placement_data[&slot_var(slot)];
            let range_checks = artifact
                .range_check_16_lookup_expressions
                .iter()
                .filter(|l| l.input.is_trivial_single_input() && l.input.linear_terms[0].1 == addr)
                .count();
            assert_eq!(range_checks, 1, "{layout} slot {slot}: RC-16 lookups");
            let types = writer_types(slot);
            assert!(types.len() >= 2, "{layout} slot {slot}: writers {types:?}");
            assert!(
                types.iter().all(|t| !matches!(*t, "u8" | "bool")),
                "{layout} slot {slot}: writers {types:?}"
            );
        }
        assert!(
            writer_types(19).contains(&"u8"),
            "{layout}: slot 19's byte writer not seen"
        );
    }

    check::<BabyBearField>(
        "compiled_circuits/unified_reduced_machine_layout_gkr.json",
        "compiled_circuits/unified_reduced_machine_ssa_gkr.json",
    );
    check::<Proth120>(
        "compiled_circuits/unified_reduced_machine_layout_gkr_proth120.json",
        "compiled_circuits/unified_reduced_machine_ssa_gkr_proth120.json",
    );
}
