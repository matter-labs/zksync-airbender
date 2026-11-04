use super::{run_test_vector_cases, TestVectorSpec};

#[test]
fn test_vector_lui() {
    run_test_vector_cases(TestVectorSpec {
        test_vectors: include_str!("data/lui-01.S"),
        match_prefix: "TEST_CASE",
        patch_match: None,
        opfields: &[5, 6],
        patch_immediate: Some(6),
        patch_immediate_with_register: false,
        initial_registers_index: &[],
        patch_initial_register: None,
        final_register_index: Some((1, 2)),
        selected_test_vectors: &[],
    });
}
