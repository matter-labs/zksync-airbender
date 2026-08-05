use gpu_gkr_compiler::{
    ContinuationResourceProfile, GpuResourceProfile, R0ResourceProfile,
    validate_continuation_profile, validate_r0_profile,
};

#[test]
fn production_profiles_validate_independently() {
    let profile = GpuResourceProfile::production();
    validate_r0_profile(&profile.r0).unwrap();
    validate_continuation_profile(&profile.continuations).unwrap();
}

#[test]
fn r0_and_continuation_are_distinct_policy_types() {
    fn accepts_r0(_: &R0ResourceProfile) {}
    fn accepts_continuation(_: &ContinuationResourceProfile) {}

    let profile = GpuResourceProfile::production();
    accepts_r0(&profile.r0);
    accepts_continuation(&profile.continuations);
}

#[test]
fn invalid_r0_capacities_are_typed_errors() {
    let mut profile = GpuResourceProfile::production().r0;
    profile.source_window_columns = 0;
    assert_eq!(
        validate_r0_profile(&profile).unwrap_err().field(),
        "source_window_columns"
    );

    let mut profile = GpuResourceProfile::production().r0;
    profile.max_program_words = 3;
    assert_eq!(
        validate_r0_profile(&profile).unwrap_err().field(),
        "max_program_words"
    );
}

#[test]
fn invalid_continuation_fragment_capacities_are_typed_errors() {
    let mut profile = GpuResourceProfile::production().continuations;
    profile.max_fragment_atoms = 0;
    assert_eq!(
        validate_continuation_profile(&profile).unwrap_err().field(),
        "max_fragment_atoms"
    );

    let mut profile = GpuResourceProfile::production().continuations;
    profile.max_expansion_factor = 0;
    assert_eq!(
        validate_continuation_profile(&profile).unwrap_err().field(),
        "max_expansion_factor"
    );
}
