use super::{run_test_vector_cases, TestVectorSpec};

#[test]
fn test_vector_jalr() {
    run_test_vector_cases(TestVectorSpec {
        test_vectors: include_str!("data/jalr-01.S"),
        match_prefix: "TEST_JALR_OP",
        patch_match: Some("jalr"),
        opfields: &[0, 2, 3, 4],
        patch_immediate: Some(4),
        patch_immediate_with_register: true,
        initial_registers_index: &[],
        patch_initial_register: None,
        final_register_index: None,
        selected_test_vectors: &[],
    });
}
