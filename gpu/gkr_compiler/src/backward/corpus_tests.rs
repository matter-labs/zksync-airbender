use std::collections::BTreeMap;
use std::path::PathBuf;

use cs::gkr_compiler::GKRCircuitArtifact;
use field::proth120::Proth120;
use field::{baby_bear::base::BabyBearField, FieldExtension, PrimeField};
use gkr_eval_ir::lower_dag;

use super::common::interp::{interpret_coeff_layer, CoeffResolver};
use super::common::model::{CoefficientRecipeId, SourceId};
use super::common::{Bf, Ext};
use super::compile_continuations;
use super::continuation::interpret_continuation_program;

pub(super) const CORPUS: &[&str] = &[
    "add_sub_lui_auipc_mop_layout_gkr.json",
    "bigint_with_extended_control_layout_gkr.json",
    "blake2_g_function_layout_gkr.json",
    "blake2_with_extended_control_layout_gkr.json",
    "inits_and_teardowns_layout_gkr.json",
    "jump_branch_slt_layout_gkr.json",
    "keccak_special5_layout_gkr.json",
    "mem_subword_only_layout_gkr.json",
    "mem_word_only_layout_gkr.json",
    "shift_binop_layout_gkr.json",
    "unified_reduced_machine_layout_gkr.json",
    "unsigned_mul_div_layout_gkr.json",
];

struct Resolver;

fn lift(value: u32) -> Ext {
    <Ext as FieldExtension<Bf>>::from_base(Bf::from_u32_with_reduction(value))
}

impl CoeffResolver<Ext> for Resolver {
    fn coefficient(&self, id: CoefficientRecipeId) -> Ext {
        lift(17 + id.0 * 13)
    }

    fn source_pair(&self, id: SourceId, row: usize) -> (Ext, Ext) {
        let base = 31 + id.0 * 19 + row as u32 * 7;
        (lift(base), lift(base + 5))
    }

    fn immediate(&self, value: u128) -> Ext {
        lift(u32::try_from(value).unwrap())
    }
}

struct Proth120Resolver;

fn wide(value: u128) -> Proth120 {
    Proth120::from_u128_with_reduction(
        value.wrapping_mul(0x9e37_79b9_7f4a_7c15_f39c_c060_5ced_c835),
    )
}

impl CoeffResolver<Proth120> for Proth120Resolver {
    fn coefficient(&self, id: CoefficientRecipeId) -> Proth120 {
        wide(17 + u128::from(id.0) * 13)
    }

    fn source_pair(&self, id: SourceId, row: usize) -> (Proth120, Proth120) {
        let base = 31 + u128::from(id.0) * 19 + row as u128 * 7;
        (wide(base), wide(base + 5))
    }

    fn immediate(&self, value: u128) -> Proth120 {
        Proth120::from_u128_with_reduction(value)
    }
}

#[test]
fn proth120_interpreter_parity() {
    let directory = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../cs/compiled_circuits");
    let artifact: GKRCircuitArtifact<Proth120> = serde_json::from_slice(
        &std::fs::read(directory.join("unified_reduced_machine_layout_gkr_proth120_2p21.json"))
            .unwrap(),
    )
    .unwrap();
    let dag = lower_dag(&artifact).unwrap();
    let continuations =
        super::compile_continuations_with_model(&dag, crate::ElementModel::PROTH120).unwrap();
    assert_eq!(continuations.layers.len(), dag.layers.len());
    let mut wide_immediates = 0;
    for layer in &continuations.layers {
        wide_immediates += layer
            .coefficients
            .immediates
            .iter()
            .filter(|&&value| value > u128::from(u32::MAX))
            .count();
        for (row, k) in [(0, 1), (3, 7), (11, 3)] {
            let expected =
                interpret_coeff_layer(&layer.coefficients, row, &Proth120Resolver).unwrap();
            let encoded = interpret_continuation_program(layer, row, &Proth120Resolver, k).unwrap();
            assert_eq!(encoded, expected, "Proth120 continuation L{}", layer.layer);
        }
    }
    assert!(wide_immediates > 0);
}

#[test]
fn continuation_corpus_matches_the_cpu_codec_oracle() {
    let directory = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../cs/compiled_circuits");
    for layout_name in CORPUS {
        let artifact: GKRCircuitArtifact<BabyBearField> =
            serde_json::from_slice(&std::fs::read(directory.join(layout_name)).unwrap()).unwrap();
        let dag = lower_dag(&artifact).unwrap_or_else(|error| panic!("{layout_name}: {error}"));
        let continuations = compile_continuations(&dag)
            .unwrap_or_else(|error| panic!("{layout_name} continuation: {error:?}"));

        for layer in &continuations.layers {
            for (row, k) in [(0, 1), (3, 7)] {
                let expected = interpret_coeff_layer(&layer.coefficients, row, &Resolver).unwrap();
                let encoded = interpret_continuation_program(layer, row, &Resolver, k).unwrap();
                assert_eq!(
                    encoded, expected,
                    "{layout_name} continuation L{}",
                    layer.layer
                );
            }
        }
    }
}

#[test]
fn proth120_backward_term_classes() {
    let directory = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../cs/compiled_circuits");
    let artifact: GKRCircuitArtifact<Proth120> = serde_json::from_slice(
        &std::fs::read(directory.join("unified_reduced_machine_layout_gkr_proth120_2p21.json"))
            .unwrap(),
    )
    .unwrap();
    let dag = lower_dag(&artifact).unwrap();
    let model = crate::ElementModel::PROTH120;
    let r0 = super::compile_r0_with_model(&dag, model).unwrap();
    let continuations = super::compile_continuations_with_model(&dag, model).unwrap();
    let semantic = |terms: &[super::common::model::CoeffTerm]| {
        let mut counts = BTreeMap::<String, usize>::new();
        for term in terms {
            *counts
                .entry(format!("{:?}", super::common::limits::term_category(term)))
                .or_default() += 1;
        }
        counts
    };
    let mut layers = Vec::new();
    for (r0, continuation) in r0.iter().zip(&continuations.layers) {
        let mut r0_wire = BTreeMap::<u16, usize>::new();
        for record in r0.window.words.chunks_exact(4) {
            *r0_wire.entry(record[0] & 0x7fff).or_default() += 1;
        }
        let r0_semantic = semantic(&r0.coefficients.terms);
        let continuation_semantic = semantic(&continuation.coefficients.terms);
        assert_eq!(
            r0_semantic.values().sum::<usize>(),
            r0.coefficients.terms.len()
        );
        assert_eq!(
            continuation_semantic.values().sum::<usize>(),
            continuation.coefficients.terms.len()
        );
        assert!(r0_wire
            .keys()
            .all(|opcode| matches!(opcode, 0 | 2 | 4 | 6 | 8 | 9)));
        let wire = |opcodes: &[u16]| -> usize {
            opcodes
                .iter()
                .map(|opcode| r0_wire.get(opcode).copied().unwrap_or(0))
                .sum()
        };
        let semantic_total = |counts: &BTreeMap<String, usize>, prefix: &str| -> usize {
            counts
                .iter()
                .filter(|(category, _)| category.starts_with(prefix))
                .map(|(_, count)| count)
                .sum()
        };
        assert_eq!(wire(&[0, 4]), semantic_total(&r0_semantic, "C0Linear"));
        assert_eq!(wire(&[2, 8, 9]), semantic_total(&r0_semantic, "C2Product"));
        assert_eq!(
            r0.coefficients.terms.len(),
            continuation.coefficients.terms.len()
        );
        assert!(continuation_semantic
            .keys()
            .all(|category| category == "C0LinearE4" || category == "DualProductE4"));
        layers.push(serde_json::json!({
            "layer": continuation.layer,
            "r0_semantic_terms": r0_semantic,
            "r0_wire_records_by_opcode": r0_wire,
            "continuation_semantic_terms": continuation_semantic,
            "continuation_groups": continuation.coefficients.groups.len(),
        }));
    }
    println!(
        "M6_BACKWARD_TERM_CLASSES {}",
        serde_json::Value::Array(layers)
    );
}
