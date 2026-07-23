pub(crate) mod eval_recipes;
pub mod immediate_factors;
// `pub` (not `pub(crate)`): re-exported as `gpu_gkr::gkr_initial_inner_products`
// (apex proof consumes `initial_inner_product_e4`).
pub mod initial_inner_products;
