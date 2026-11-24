use super::*;
use crate::proof::memory_policy::GkrMemoryPolicy;

fn check_policies(circuit: CanonicalCircuit, mode: circuit_common::SoundnessMode) {
    let fixture = prepare_canonical_proof_fixture(circuit, mode);
    let base = &fixture.base;
    let preparation_peak = base.context.get_used_mem_peak();
    let baseline = base.context.get_used_mem_current();
    base.context.reset_used_mem_peak();
    let presets = [21usize << 30, 30usize << 30]
        .map(|arena| presets::policy(base.circuit_type, ProofProfile::Standard, arena));
    let mut policies = vec![ProofMemoryPolicy::default()];
    for policy in ProofMemoryPolicy::candidates()
        .chain(GkrMemoryPolicy::candidates().map(|gkr| ProofMemoryPolicy {
            gkr,
            ..Default::default()
        }))
        .chain(presets)
    {
        if !policies.contains(&policy) {
            policies.push(policy);
        }
    }
    let mut checked = 0;
    for pair in policies.chunks(2) {
        let jobs = [pair[0], *pair.get(1).unwrap_or(&pair[0])]
            .map(|policy| base.schedule_prove_with_memory_policy(policy).unwrap());
        for job in jobs {
            let (proof, _) = job.finish().unwrap();
            fixture.assert_proof(&proof);
            checked += 1;
            assert_eq!(
                base.context.get_used_mem_current(),
                baseline,
                "device memory must return to baseline after each policy finish"
            );
        }
    }
    assert!(checked >= policies.len());
    record_test_resources(base, preparation_peak, checked);
}

macro_rules! policy_tests {
    ($(($p:ident, $e:ident, $circuit:ident)),* $(,)?) => { $(
        #[test]
        #[ignore = "production policy candidates and presets against committed proof bytes"]
        fn $p() { check_policies(CanonicalCircuit::$circuit, circuit_common::SoundnessMode::PessimisticConjecture); }
        #[test]
        #[ignore = "production policy candidates and presets against committed proof bytes"]
        fn $e() { check_policies(CanonicalCircuit::$circuit, circuit_common::SoundnessMode::EthproofsSoundnessCalc); }
    )* };
}

policy_tests! {
    (policies_add_sub_pessimistic_conjecture, policies_add_sub_ethproofs_soundcalc, AddSubLuiAuipcMop),
    (policies_inits_and_teardowns_pessimistic_conjecture, policies_inits_and_teardowns_ethproofs_soundcalc, InitsAndTeardowns),
    (policies_keccak_special5_pessimistic_conjecture, policies_keccak_special5_ethproofs_soundcalc, KeccakSpecial5),
    (policies_blake2_with_compression_pessimistic_conjecture, policies_blake2_with_compression_ethproofs_soundcalc, Blake2WithExtendedControl),
}
