mod common;
use common::*;
use gkr_eval_isa::bwd::compile::{compile_distilled, compile_distilled_traced};
use gkr_eval_isa::bwd::distill::distill;
use gkr_eval_isa::bwd::trace::{
    freeze_demand, live_profile, BwdEvent, BwdServedFrom, BwdServeKind,
};
use cs::gkr_compiler::dag_ir::BwdRegime;

/// Tracing is observation only: program byte-identical to the untraced compile.
#[test]
fn traced_compile_is_byte_identical() {
    for (li, layer, cross) in layers_with_bwd_roots("add_sub_lui_auipc_mop_layout_gkr.json") {
        let d = distill(&layer, BwdRegime::Ext, &cross, None);
        let base = compile_distilled(&d, 16, None).unwrap();
        let (traced, trace) = compile_distilled_traced(&d, 16, None).unwrap();
        assert_eq!(encode(&base.program), encode(&traced.program), "L{li}");
        assert_eq!(trace.budget, 16);
        assert_eq!(trace.free.len(), traced.program.instrs.len(), "L{li}");
        assert!(trace.events.iter().any(|e| matches!(e, BwdEvent::Serve { .. })), "L{li}");
    }
}

/// TrafficRead events recount to EXACTLY the tally's traffic (certificate seed).
#[test]
fn trace_traffic_reads_match_tally() {
    for (li, layer, cross) in layers_with_bwd_roots("add_sub_lui_auipc_mop_layout_gkr.json") {
        let d = distill(&layer, BwdRegime::Ext, &cross, None);
        let (c, trace) = compile_distilled_traced(&d, 16, None).unwrap();
        let counted: usize = trace.events.iter()
            .filter_map(|e| match e { BwdEvent::TrafficRead { cells, .. } => Some(*cells as usize), _ => None })
            .sum();
        assert_eq!(counted, c.stats_ext.global + c.stats_ext.fold_traffic, "L{li}");
    }
}

/// Serve fingerprints walk the spine terms in order (term index nondecreasing 0..n).
#[test]
fn trace_terms_are_monotone() {
    for (_li, layer, cross) in layers_with_bwd_roots("add_sub_lui_auipc_mop_layout_gkr.json") {
        let d = distill(&layer, BwdRegime::Ext, &cross, None);
        let (_c, trace) = compile_distilled_traced(&d, 16, None).unwrap();
        let mut last = 0u32;
        for e in &trace.events {
            if let BwdEvent::Serve { fp, .. } = e {
                assert!(fp.term >= last, "term regressed {} -> {}", last, fp.term);
                last = fp.term;
            }
        }
    }
}

/// Leaf demand instants (DOMAIN leaves only): k-th FoldSource use in the program
/// == k-th Recomputed serve of that leaf in the trace (per-leaf counts must agree
/// exactly). Non-domain gathers are accounted in nondomain_gather_cells instead.
#[test]
fn frozen_leaf_instants_align_with_serves() {
    for (li, layer, cross) in layers_with_bwd_roots("add_sub_lui_auipc_mop_layout_gkr.json") {
        let d = distill(&layer, BwdRegime::Ext, &cross, None);
        let (c, trace) = compile_distilled_traced(&d, 16, None).unwrap();
        let frozen = freeze_demand(&d, &trace, &c.program, &c.specials);
        assert_eq!(frozen.epoch, trace.epoch);
        for (v, instants) in &frozen.leaf_instants {
            let serves = frozen.domain_serves.iter()
                .filter(|(fp, from)| fp.value == *v && matches!(from, BwdServedFrom::Recomputed))
                .count();
            assert_eq!(instants.len(), serves, "L{li} leaf {v:?}");
        }
        assert!(frozen.free.iter().all(|&f| f <= 16), "L{li}");
    }
}
