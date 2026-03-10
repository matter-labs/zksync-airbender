use super::{run_test_vector_cases, TestVectorSpec};

#[test]
fn test_vector_sh() {
    run_test_vector_cases(TestVectorSpec {
        test_vectors: include_str!("data/sh-align-01.S"),
        match_prefix: "TEST_STORE",
        patch_match: None,
        opfields: &[8, 4, 3, 6],
        patch_immediate: Some(6),
        patch_immediate_with_register: true,
        initial_registers_index: &[(4, 5), (3, 10)],
        patch_initial_register: Some("2097152"),
        final_register_index: None,
        selected_test_vectors: &[],
    });
}
