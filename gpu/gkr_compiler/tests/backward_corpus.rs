use std::collections::BTreeMap;
use std::path::PathBuf;

use cs::gkr_compiler::GKRCircuitArtifact;
use field::baby_bear::base::BabyBearField;
use field::PrimeField;
use gkr_eval_ir::lower_dag;
use gpu_gkr_compiler::{
    compile_continuations, compile_r0, lower_main_continuation_window_program,
    lower_main_tail_program, NormalizedCoefficientRecipe, WindowCoefficientPlan,
};
use sha3::{Digest, Sha3_256};

const CORPUS: &[&str] = &[
    "add_sub_lui_auipc_mop",
    "bigint_with_extended_control",
    "blake2_g_function",
    "blake2_with_extended_control",
    "inits_and_teardowns",
    "jump_branch_slt",
    "keccak_chi5",
    "keccak_column_parity",
    "keccak_special5",
    "keccak_theta_rho",
    "mem_subword_only",
    "mem_word_only",
    "shift_binop",
    "unified_reduced_machine",
    "unsigned_mul_div",
];

fn push_u16s(out: &mut Vec<u8>, values: &[u16]) {
    out.extend_from_slice(&(values.len() as u32).to_le_bytes());
    for value in values {
        out.extend_from_slice(&value.to_le_bytes());
    }
}

fn push_u32s(out: &mut Vec<u8>, values: impl ExactSizeIterator<Item = u32>) {
    out.extend_from_slice(&(values.len() as u32).to_le_bytes());
    for value in values {
        out.extend_from_slice(&value.to_le_bytes());
    }
}

fn push_debug(out: &mut Vec<u8>, value: &impl std::fmt::Debug) {
    let text = format!("{value:?}");
    out.extend_from_slice(&(text.len() as u32).to_le_bytes());
    out.extend_from_slice(text.as_bytes());
}

fn push_debug_list<T: std::fmt::Debug>(out: &mut Vec<u8>, values: &[T]) {
    out.extend_from_slice(&(values.len() as u32).to_le_bytes());
    for value in values {
        push_debug(out, value);
    }
}

fn canonical_word(value: u32) -> u32 {
    let value = u32::try_from(value).unwrap();
    assert!(value < BabyBearField::CHARACTERISTICS_U32);
    value
}

fn native_word(canonical: u32) -> u32 {
    BabyBearField::from_u32_with_reduction(canonical_word(canonical)).as_u32_raw_repr_reduced()
}

fn push_recipe(out: &mut Vec<u8>, recipe: &NormalizedCoefficientRecipe) {
    out.extend_from_slice(&(recipe.terms.len() as u32).to_le_bytes());
    for product in &recipe.terms {
        out.extend_from_slice(&canonical_word(product.scalar).to_le_bytes());
        push_debug_list(out, &product.challenges);
        push_debug_list(out, &product.inits_and_teardowns_top_bits);
    }
}

fn stable_backward_program_bytes(dag: &gkr_eval_ir::DagCircuit) -> Vec<u8> {
    let mut out = Vec::new();
    for (index, r0) in compile_r0(dag).unwrap().iter().enumerate() {
        out.extend_from_slice(b"R0");
        out.extend_from_slice(&(index as u32).to_le_bytes());
        let window = &r0.window;
        out.extend_from_slice(&(window.layer as u32).to_le_bytes());
        push_u16s(&mut out, &window.words);
        push_u16s(&mut out, &window.source_slots);
        out.extend_from_slice(&(window.source_lanes.len() as u32).to_le_bytes());
        for lane in &window.source_lanes {
            out.extend_from_slice(&lane.word.to_le_bytes());
            out.extend_from_slice(&lane.source.to_le_bytes());
        }
        push_debug_list(&mut out, &window.windows);
        push_u32s(&mut out, window.immediates.iter().copied());
        push_u32s(&mut out, window.sections.iter().copied());
        out.extend_from_slice(&(window.coefficient_plans.len() as u32).to_le_bytes());
        for plan in &window.coefficient_plans {
            match plan {
                WindowCoefficientPlan::Direct(recipe) => {
                    out.push(0);
                    push_recipe(&mut out, recipe);
                }
                WindowCoefficientPlan::Scaled { recipe, scalar } => {
                    out.push(1);
                    push_recipe(&mut out, recipe);
                    out.extend_from_slice(&canonical_word(*scalar).to_le_bytes());
                }
                WindowCoefficientPlan::LinearBasis { recipe, limb } => {
                    out.push(2);
                    push_recipe(&mut out, recipe);
                    out.push(*limb);
                }
            }
        }
        push_debug(&mut out, &window.shape);
        push_debug(&mut out, &r0.scalar_seed);
        push_debug(&mut out, &r0.kernel);
        push_debug(&mut out, &r0.partition_candidates);
    }
    let continuations = compile_continuations(dag).unwrap();
    for layer in &continuations.layers {
        out.extend_from_slice(b"CONT");
        out.extend_from_slice(&(layer.layer as u32).to_le_bytes());
        push_u16s(&mut out, &layer.program.words);
        push_debug(&mut out, &layer.binding);
        let coefficients = &layer.coefficients;
        push_debug(&mut out, &coefficients.c_init);
        out.extend_from_slice(&(coefficients.coefficients.len() as u32).to_le_bytes());
        for recipe in &coefficients.coefficients {
            push_recipe(&mut out, recipe);
        }
        push_debug_list(&mut out, &coefficients.sources);
        push_debug_list(&mut out, &coefficients.terms);
        push_debug_list(&mut out, &coefficients.groups);
        push_u32s(
            &mut out,
            coefficients
                .immediates
                .iter()
                .map(|&value| native_word(value)),
        );

        out.extend_from_slice(b"MCW");
        let window = lower_main_continuation_window_program(layer).unwrap();
        push_u16s(&mut out, &window.program.words);
        push_debug_list(&mut out, &window.partitions);
        push_debug(&mut out, &window.c_init);
        push_u32s(
            &mut out,
            window.immediates.iter().map(|&value| native_word(value)),
        );
        push_debug_list(&mut out, &window.sources);
        push_debug(&mut out, &window.shape);

        out.extend_from_slice(b"TAIL");
        let tail = lower_main_tail_program(layer);
        out.extend_from_slice(&(tail.layer as u32).to_le_bytes());
        push_u16s(&mut out, &tail.list_offsets);
        push_u16s(&mut out, &tail.program_words);
        push_u32s(
            &mut out,
            tail.immediates.iter().map(|&value| native_word(value)),
        );
        out.extend_from_slice(&tail.source_count.to_le_bytes());
        out.extend_from_slice(&tail.c_init_coeff_id.to_le_bytes());
    }
    out
}

#[test]
fn babybear_backward_programs_match_committed_hashes() {
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let directory = manifest.join("../../cs/compiled_circuits");
    let fixture = manifest.join("tests/fixtures/backward_programs.json");
    let mut hashes = BTreeMap::new();
    for &stem in CORPUS {
        let layout: GKRCircuitArtifact<BabyBearField> = serde_json::from_slice(
            &std::fs::read(directory.join(format!("{stem}_layout_gkr.json"))).unwrap(),
        )
        .unwrap();
        let dag = lower_dag(&layout).unwrap_or_else(|error| panic!("{stem}: {error}"));
        let digest = Sha3_256::digest(stable_backward_program_bytes(&dag));
        hashes.insert(
            stem.to_owned(),
            digest
                .iter()
                .map(|byte| format!("{byte:02x}"))
                .collect::<String>(),
        );
    }
    if std::env::var_os("AB_RECORD_BACKWARD_PROGRAM_HASHES").is_some() {
        let mut text = serde_json::to_string_pretty(&hashes).unwrap();
        text.push('\n');
        std::fs::write(&fixture, text).unwrap();
    }
    let committed: BTreeMap<String, String> =
        serde_json::from_slice(&std::fs::read(&fixture).unwrap()).unwrap();
    assert_eq!(committed.len(), CORPUS.len());
    for (stem, hash) in &hashes {
        assert_eq!(committed.get(stem), Some(hash), "{stem}");
    }
}
