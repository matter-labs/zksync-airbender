//! SP2 strategy-coverage census: classify every emitted SpecialDescriptor across the
//! golden fixtures by SpecialStrategy, so the minimal real-data validation set is chosen
//! from evidence. Prints a coverage table; asserts all four strategies are reachable.

mod census_helpers;

use gkr_eval_isa::fwd::source::SpecialStrategy;

#[derive(Default, Debug)]
struct StrategyCounts { single: usize, aggregate: usize, setup: usize, decoder: usize }
impl StrategyCounts {
    fn add(&mut self, o: &StrategyCounts) {
        self.single += o.single; self.aggregate += o.aggregate;
        self.setup += o.setup; self.decoder += o.decoder;
    }
}

#[test]
fn census_reaches_all_four_strategies_at_layer0() {
    let mut totals = StrategyCounts::default();   // all layers (informational)
    let mut layer0 = StrategyCounts::default();   // layer 0 only (the SP2-scoped gate target)
    let mut per_fixture: Vec<(String, usize, StrategyCounts)> = Vec::new();

    for name in census_helpers::FIXTURES {
        let Some(artifact) = census_helpers::load_fixture(name) else { continue };
        let dag = census_helpers::lower(&artifact);
        for (layer_idx, _layer) in dag.layers.iter().enumerate() {
            let compiled = census_helpers::compile_one_layer(&artifact, &dag, layer_idx);
            let mut c = StrategyCounts::default();
            for desc in census_helpers::special_strategies(&compiled) {
                match desc {
                    SpecialStrategy::PeekSingleColumn { .. } => c.single += 1,
                    SpecialStrategy::PeekAggregate { .. } => c.aggregate += 1,
                    SpecialStrategy::PeekSetup => c.setup += 1,
                    SpecialStrategy::PeekDecoder { .. } => c.decoder += 1,
                }
            }
            totals.add(&c);
            if layer_idx == 0 { layer0.add(&c); }
            if c.single + c.aggregate + c.setup + c.decoder > 0 {
                per_fixture.push((name.to_string(), layer_idx, c));
            }
        }
    }

    for (name, layer, c) in &per_fixture {
        println!("{name} L{layer}: single={} aggregate={} setup={} decoder={}", c.single, c.aggregate, c.setup, c.decoder);
    }
    println!("ALL-LAYER TOTALS: {totals:?}");
    println!("LAYER-0 TOTALS:   {layer0:?}");

    // SP2 gates are layer-0-scoped (Tasks 7-9), so all four strategies must be reachable AT LAYER 0.
    // A strategy present only at layer > 0 (totals.X > 0 but layer0.X == 0) is an escalation:
    // covering it needs multi-layer real-data storage, a scope expansion beyond SP2 (design §12).
    assert!(layer0.single > 0, "no PeekSingleColumn at layer 0 (all-layer total {})", totals.single);
    assert!(layer0.aggregate > 0, "no PeekAggregate at layer 0 (all-layer total {})", totals.aggregate);
    assert!(layer0.setup > 0, "no PeekSetup at layer 0 (all-layer total {})", totals.setup);
    assert!(layer0.decoder > 0, "no PeekDecoder at layer 0 (all-layer total {})", totals.decoder);
}
