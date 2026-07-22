use std::path::PathBuf;

use cs::gkr_compiler::dag_ir::{lower_dag, BwdRegime, DagCircuit, DagLayer};
use gkr_eval_isa::bwd::distill::{distill, DistilledLayer};
use gkr_eval_isa::eval_plan::{
    compile_backward_plan_artifact, load_backward_evaluation_artifact, select_backward_plan,
    CompiledBackwardEvaluation,
};
use gkr_eval_isa::fwd::compile::build_cross_layer_field_map;

/// Fully replayed, artifact-certified backward-VM input for add/sub layer 0.
///
/// This loader deliberately consumes only published artifacts: it does not
/// invoke a schedule or pager solver. `compile_backward_plan_artifact` rebuilds
/// and certifies the selected plan against its published digest and score.
pub(crate) struct AddSubBwdVmCase {
    pub(crate) dag: DagCircuit,
    pub(crate) canonical: DagLayer,
    pub(crate) distilled: DistilledLayer,
    pub(crate) compiled: CompiledBackwardEvaluation,
    pub(crate) trace_len: usize,
    pub(crate) regime: BwdRegime,
    pub(crate) budget_cells: usize,
}

const ADD_SUB_LAYOUT: &str = "add_sub_lui_auipc_mop_layout_gkr.json";
const ADD_SUB_BACKWARD_PLAN: &str = "add_sub_lui_auipc_mop_bwd_eval_plan_c2-c16_gkr.json";

fn compiled_circuit_path(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../cs/compiled_circuits")
        .join(name)
}

/// Reconstruct one layer-0 backward VM case from the committed add/sub
/// layout and backward-plan artifacts.
pub(crate) fn load_add_sub_l0_case(regime: BwdRegime, budget_cells: usize) -> AddSubBwdVmCase {
    let layout_path = compiled_circuit_path(ADD_SUB_LAYOUT);
    let layout_bytes = std::fs::read(&layout_path)
        .unwrap_or_else(|error| panic!("read {}: {error}", layout_path.display()));
    let layout: crate::upstream::GKRCircuitArtifact<crate::primitives::field::BF> =
        serde_json::from_slice(&layout_bytes)
            .unwrap_or_else(|error| panic!("parse {}: {error}", layout_path.display()));
    let dag = lower_dag(&layout).unwrap_or_else(|error| panic!("lower add/sub DAG: {error}"));
    let cross = build_cross_layer_field_map(&dag);
    let canonical = dag
        .layers
        .first()
        .cloned()
        .expect("add/sub artifact must have canonical layer 0");
    let distilled = distill(&canonical, regime, &cross, None);
    let trace_len = dag.globals.trace_len;

    let plan_path = compiled_circuit_path(ADD_SUB_BACKWARD_PLAN);
    let plans = load_backward_evaluation_artifact(&plan_path)
        .unwrap_or_else(|error| panic!("load {}: {error:?}", plan_path.display()));
    let plan = select_backward_plan(&plans, 0, regime, budget_cells)
        .unwrap_or_else(|error| panic!("select add/sub L0 {regime:?} c{budget_cells}: {error:?}"));
    let compiled =
        compile_backward_plan_artifact(&plans.circuit, 0, &canonical, &distilled, trace_len, plan)
            .unwrap_or_else(|error| {
                panic!("replay add/sub L0 {regime:?} c{budget_cells}: {error:?}")
            })
            .compiled;

    AddSubBwdVmCase {
        dag,
        canonical,
        distilled,
        compiled,
        trace_len,
        regime,
        budget_cells,
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use cs::gkr_compiler::dag_ir::{BwdRegime, ReadPlace};
    use gkr_eval_isa::fwd::encode::decode;
    use gkr_eval_isa::fwd::isa::{Instr, OperandLine, Program};

    use super::{load_add_sub_l0_case, AddSubBwdVmCase};
    use crate::prover::gkr::forward::vm::desc::PROGRAM_CAP;

    #[test]
    fn add_sub_l0_c2_c16_program_census_matches_published_artifacts() {
        let expected_r0 = [
            1744, 1740, 1726, 1716, 1716, 1716, 1716, 1716, 1716, 1716, 1716, 1716, 1716, 1716,
            1716,
        ];
        let expected_ext = [
            1537, 1457, 1466, 1476, 1555, 1553, 1561, 1564, 1564, 1565, 1565, 1565, 1565, 1565,
            1565,
        ];
        for (regime, expected) in [(BwdRegime::R0, expected_r0), (BwdRegime::Ext, expected_ext)] {
            let got = (2..=16)
                .map(|budget| {
                    let case = load_add_sub_l0_case(regime, budget);
                    assert_case_program_bindings(&case);
                    case.compiled.encoded.len()
                })
                .collect::<Vec<_>>();
            assert_eq!(got, expected);
        }
    }

    fn assert_case_program_bindings(case: &AddSubBwdVmCase) {
        assert_eq!(
            decode(&case.compiled.encoded).unwrap(),
            case.compiled.compiled.program
        );
        assert!(case.compiled.encoded.len() <= PROGRAM_CAP);
        assert_no_logical_sources(&case.compiled.compiled.program);
        assert_source_windows_are_bound(case);
    }

    fn assert_no_logical_sources(program: &Program) {
        visit_operands(program, |operand| match operand {
            OperandLine::LogicalGlobal { .. } | OperandLine::LogicalFold { .. } => {
                panic!("backward program has unbound logical source: {operand:?}")
            }
            OperandLine::Source { .. }
            | OperandLine::Smem { .. }
            | OperandLine::Ldc { .. }
            | OperandLine::Special { .. } => {}
        });
    }

    fn assert_source_windows_are_bound(case: &AddSubBwdVmCase) {
        let windows = &case.compiled.compiled.source_windows;
        let mut referenced = BTreeMap::<(u8, u8), ReadPlace>::new();
        for (window_index, window) in windows.windows().iter().enumerate() {
            let window_index = u8::try_from(window_index).expect("source window index fits u8");
            for absolute_column in window.referenced_columns() {
                let column = absolute_column
                    .checked_sub(window.first_column)
                    .and_then(|column| u8::try_from(column).ok())
                    .expect("referenced source column fits its source window");
                let place = windows
                    .resolve_read_place(window_index, column)
                    .expect("source window must reverse to a read place");
                assert_eq!(referenced.insert((window_index, column), place), None);
            }
        }

        let mut first_accesses = BTreeMap::<(u8, u8), usize>::new();
        let mut uses = BTreeMap::<(u8, u8), usize>::new();
        visit_operands(&case.compiled.compiled.program, |operand| {
            if let OperandLine::Source {
                window,
                column,
                first_access,
            } = operand
            {
                assert!(
                    referenced.contains_key(&(*window, *column)),
                    "program source must reverse through source_windows"
                );
                *uses.entry((*window, *column)).or_default() += 1;
                if *first_access {
                    *first_accesses.entry((*window, *column)).or_default() += 1;
                }
            }
        });

        for source in referenced.keys() {
            assert!(
                uses.contains_key(source),
                "source-window entry is not read by the program"
            );
            assert_eq!(
                first_accesses.get(source).copied().unwrap_or_default(),
                1,
                "each backward read source must have one first_access"
            );
        }
    }

    fn visit_operands(program: &Program, mut visit: impl FnMut(&OperandLine)) {
        for instruction in &program.instrs {
            match instruction {
                Instr::Add { operands, .. } | Instr::Mul { operands, .. } => {
                    for operand in operands {
                        visit(operand);
                    }
                }
                Instr::Fma { pairs, .. } => {
                    for (lhs, rhs) in pairs {
                        visit(lhs);
                        visit(rhs);
                    }
                }
                Instr::Mov { src, .. } => {
                    if let Some(source) = src {
                        visit(source);
                    }
                }
            }
        }
    }
}
