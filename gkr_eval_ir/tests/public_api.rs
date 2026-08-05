#[allow(unused_imports)]
use gkr_eval_ir::{
    eval_layer_expr, eval_layer_root, expr_field, fold_vs_from_originals, join, lower_dag,
    lower_dag_legacy, read_place_field, simplify_circuit, source_field, validate,
    validate_simplified, ArenaBuilder, Resolvers,
};

#[test]
fn canonical_ir_surface_is_available_without_gpu_policy() {
    fn exported<T>() {}

    exported::<ArenaBuilder>();
    exported::<Resolvers<'static>>();
}
