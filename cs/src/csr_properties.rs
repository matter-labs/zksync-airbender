use crate::{machine::NON_DETERMINISM_CSR, tables::*};
use field::PrimeField;

pub fn create_special_csr_properties_table<F: PrimeField>(
    id: u32,
    support_non_determinism_csr: bool,
    supported_delegations: &[u32],
) -> LookupTable<F, 3> {
    for el in supported_delegations.iter() {
        assert!(*el < (1 << 12));
    }

    let keys = key_for_continuous_log2_range(12);
    let supported_delegations = supported_delegations.to_vec();
    const TABLE_NAME: &'static str = "Special CSR properties";
    LookupTable::<F, 3>::create_table_from_key_and_key_generation_closure(
        &keys,
        TABLE_NAME.to_string(),
        1,
        move |key| {
            let input = key[0].as_u64_reduced();
            assert!(input < (1u64 << 12));
            let csr_index = input as u32;
            let is_nondeterminism_csr = csr_index == NON_DETERMINISM_CSR as u32;
            let is_allowed_for_delegation =
                supported_delegations.contains(&csr_index) && is_nondeterminism_csr == false;
            if is_nondeterminism_csr {
                assert!(is_allowed_for_delegation == false);
                assert!(support_non_determinism_csr);
            }
            let is_supported =
                (is_nondeterminism_csr & support_non_determinism_csr) | is_allowed_for_delegation;

            let result = [
                F::from_u64_unchecked(is_supported as u64),
                F::from_u64_unchecked(is_allowed_for_delegation as u64),
                F::ZERO,
            ];

            (input as usize, result)
        },
        Some(first_key_index_gen_fn::<F, 3>),
        id,
    )
}
