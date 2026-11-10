use field::baby_bear::{base::BabyBearField as F, ext4::BabyBearExt4 as E};
use field::{Field, FieldExtension};
use verifier::add_sub_lui_auipc_mop::pessimistic_conjecture::common::{
    fold_whir_accumulator, push_whir_base_pow_entry, push_whir_pow_entry,
};
use verifier_common::whir::WhirAccumulator;

fn ext(x: u64) -> E {
    E::from_array_of_base(core::array::from_fn(|i| F::new((x + i as u64) as u32)))
}

#[test]
fn mixed_accumulator_matches_extension_reference_each_round() {
    let z: Vec<_> = (0..8).map(|i| ext(41 + i)).collect();
    let mut acc = WhirAccumulator::<F, E, 16, 8>::new(E::ONE);
    let mut reference = Vec::new();
    let mut initial_prefactor = E::ONE;
    for round in 0..8 {
        // Include zero and one, then nontrivial base and extension points.
        let base = F::new(round as u32);
        let coefficient = ext(101 + round as u64);
        push_whir_base_pow_entry(&mut acc, base, coefficient);
        reference.push((E::from_base(base), E::ONE));
        let point = ext(17 + round as u64);
        push_whir_pow_entry(&mut acc, point, coefficient);
        reference.push((point, E::ONE));
        let alpha = ext(73 + round as u64);
        let eq = |s: E| {
            let mut left = E::ONE;
            left.sub_assign(&s);
            let mut right = E::ONE;
            right.sub_assign(&alpha);
            left.mul_assign(&right);
            left.add_assign_product(&s, &alpha);
            left
        };
        initial_prefactor.mul_assign(&eq(z[round]));
        for (s, prefactor) in &mut reference {
            prefactor.mul_assign(&eq(*s));
            s.square();
        }
        fold_whir_accumulator(&mut acc, alpha, &z);
        assert_eq!(acc.z_initial_idx, round + 1);
        assert_eq!(acc.z_initial_prefactor, initial_prefactor);
        for i in 0..=round {
            let base_entry = acc.base_pow_entries.get(i);
            let ext_entry = acc.pow_entries.get(i);
            assert_eq!(
                (
                    E::from_base(base_entry.current_scalar),
                    base_entry.prefactor
                ),
                reference[2 * i]
            );
            assert_eq!(
                (ext_entry.current_scalar, ext_entry.prefactor),
                reference[2 * i + 1]
            );
            assert_eq!(base_entry.coefficient, ext(101 + i as u64));
        }
    }
}
