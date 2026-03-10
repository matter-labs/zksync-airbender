use super::{run_test_vector_cases, TestVectorSpec};

#[test]
fn test_vector_auipc() {
    run_test_vector_cases(TestVectorSpec {
        test_vectors: include_str!("data/auipc-01.S"),
        match_prefix: "TEST_AUIPC",
        patch_match: None,
        opfields: &[0, 1, 3],
        patch_immediate: Some(3),
        patch_immediate_with_register: false,
        initial_registers_index: &[],
        patch_initial_register: None,
        final_register_index: Some((1, 2)),
        selected_test_vectors: &[],
    });
}
