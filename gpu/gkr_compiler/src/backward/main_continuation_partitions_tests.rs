use super::*;

fn program() -> Vec<u16> {
    vec![
        0,
        0,
        u16::MAX,
        0x4000,
        2,
        3,
        0,
        0,
        u16::MAX,
        0x2000,
        1,
        2,
        0,
        2,
        u16::MAX,
    ]
}

#[test]
fn cpu_partition_groups_and_first_owner_folds() {
    let words = program();
    let atoms = atoms(&words, 3).unwrap();
    let plans = assemble_plans(&words, 3, &atoms, &[vec![1, 0, 1]]).unwrap();
    let p = &plans[0];
    assert_eq!(p.parts[0].words, words[3..12]);
    assert_eq!(p.parts[1].words, [0, 0, u16::MAX, 0, 2, u16::MAX]);
    assert_eq!(p.parts[0].fold_sources, [0, 1, 2]);
    assert!(p.parts[1].fold_sources.is_empty());
    assert_eq!(p.source_incidences, 5);
}

#[test]
fn cpu_partition_rejects_bad_assignments_and_accepts_new_programs() {
    let mut words = program();
    let parsed = atoms(&words, 3).unwrap();
    assert!(assemble_plans(&words, 3, &parsed, &[vec![1, 0]]).is_err());
    assert!(assemble_plans(&words, 3, &parsed, &[vec![0, 0, 3]]).is_err());
    assert!(assemble_plans(&words, 4, &parsed, &[vec![1, 0, 1]]).is_err());
    words[10] = 20;
    assert!(atoms(&words, 3).is_err());
    let fresh: Vec<u16> = (0..19).flat_map(|s| [0, s, u16::MAX]).collect();
    let p = compile_main_continuation_partitions(&fresh, 19).unwrap();
    assert!(p.iter().any(|p| p.parts.len() == 8));
    assert_eq!(p, compile_main_continuation_partitions(&fresh, 19).unwrap());
}

#[test]
fn cpu_partition_policy_types_work_floor_residency_and_ties() {
    let words: Vec<_> = (0..16).flat_map(|s| [0, s, u16::MAX]).collect();
    let atoms = atoms(&words, 16).unwrap();
    let assignments = [2, 4, 8].map(|k| (0..16).map(|s| (s * k / 16) as u8).collect());
    let plans = assemble_plans(&words, 16, &atoms, &assignments).unwrap();
    let choose = |e4, rows, tiles, resident, l2| {
        select_main_continuation_partition(&plans, 16, e4, rows, tiles, resident, l2)
    };
    // Equal scores for K2 and K4 select fewer launches.
    assert_eq!(
        choose(16, 1 << 18, 8192, 376, 128 << 20)
            .unwrap()
            .parts
            .len(),
        2
    );
    assert!(choose(0, 1 << 18, 8192, 376, 128 << 20).is_none());
    assert!(choose(16, 1 << 14, 512, 376, 128 << 20).is_none());
    assert!(choose(16, 1 << 18, 8192, 8193, 128 << 20).is_none());
    assert!(choose(16, 1 << 18, 8192, 376, 1 << 20).is_none());
    assert_eq!(
        choose(16, 1 << 18, 8192, 376, 128 << 20)
            .unwrap()
            .parts
            .len(),
        2
    );
}

#[test]
fn cpu_partition_corpus_construction() {
    use crate::{compile_continuations, lower_main_continuation_window_program};
    use cs::gkr_compiler::GKRCircuitArtifact;
    use field::baby_bear::base::BabyBearField;
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../cs/compiled_circuits");
    let mut count = 0;
    for filename in super::super::corpus_tests::CORPUS {
        let artifact: GKRCircuitArtifact<BabyBearField> =
            serde_json::from_slice(&std::fs::read(root.join(filename)).unwrap()).unwrap();
        let dag = gkr_eval_ir::lower_dag(&artifact).unwrap();
        for layer in compile_continuations(&dag).unwrap().layers {
            let p = lower_main_continuation_window_program(&layer).unwrap();
            assert_eq!(
                p.partitions.is_empty(),
                atoms(&p.program.words, p.sources.len()).unwrap().len() < 2,
                "{filename} L{}",
                layer.layer
            );
            for plan in &p.partitions {
                let mut folded: Vec<_> = plan
                    .parts
                    .iter()
                    .flat_map(|part| part.fold_sources.iter().copied())
                    .collect();
                folded.sort_unstable();
                assert_eq!(folded, (0..p.sources.len() as u16).collect::<Vec<_>>());
                let original = atoms(&p.program.words, p.sources.len()).unwrap();
                let mut expected: Vec<_> = original
                    .iter()
                    .map(|a| p.program.words[a.start..a.end].to_vec())
                    .collect();
                let mut actual = Vec::new();
                let mut available = BTreeSet::new();
                for part in &plan.parts {
                    available.extend(part.fold_sources.iter().copied());
                    for atom in atoms(&part.words, p.sources.len()).unwrap() {
                        assert!(atom.sources.is_subset(&available));
                        actual.push(part.words[atom.start..atom.end].to_vec());
                    }
                }
                expected.sort();
                actual.sort();
                assert_eq!(
                    actual, expected,
                    "whole atom multiset including group headers"
                );
            }
            count += 1;
        }
    }
    assert!(count >= super::super::corpus_tests::CORPUS.len());
}
