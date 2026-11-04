use super::{run_test_vector_cases, TestVectorSpec};

#[test]
fn test_vector_lh() {
    run_test_vector_cases(TestVectorSpec {
        test_vectors: include_str!("data/lh-align-01.S"),
        match_prefix: "TEST_LOAD",
        patch_match: None,
        opfields: &[7, 4, 3, 5],
        patch_immediate: Some(5),
        patch_immediate_with_register: true,
        initial_registers_index: &[(3, 9)],
        patch_initial_register: Some("2048"),
        final_register_index: None,
        selected_test_vectors: &[],
    });
}
