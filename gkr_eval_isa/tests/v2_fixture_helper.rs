use gkr_eval_isa::test_support::{all_fixtures, fixture_path};

#[test]
fn fixture_helper_is_visible_cross_crate() {
    let p = fixture_path("add_sub_lui_auipc_mop_codegen_ir_gkr.json");
    assert!(p.exists(), "fixture path must resolve");
    let all = all_fixtures();
    assert_eq!(all.len(), 22, "expected 22 codegen_ir fixtures");
}
