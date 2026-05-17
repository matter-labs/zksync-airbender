// The legacy host-snapshot test infrastructure that used to live in this file
// (`GpuGKRBaseLayerTailSnapshot`, `wait()`, `prepare_base_layer_claims`, and
// `base_layer_claims_match_cpu`) was wired around per-column D2H readbacks of
// the base-layer polynomial claims plus a per-test D2H of the virtual-setup
// claims. After the slab-routing refactor, those readbacks are unconditional
// dead code in the production scheduler (every callable allocates a real
// slab; cached-relation extras are gathered on device). The test
// infrastructure has been removed alongside its consumers in `stagewise.rs`.
// End-to-end coverage of the base-layer-claims path now flows through
// `prover::tests::smoke::run_basic_unrolled_proof_job_multi_schedule_test`,
// which exercises the full `prove()` orchestration including base-layer
// claim aggregation against CPU parity.
