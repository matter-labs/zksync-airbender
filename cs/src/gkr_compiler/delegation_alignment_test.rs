use crate::cs::circuit_impl::BasicAssembly;
use crate::cs::circuit_trait::Circuit;
use crate::gkr_circuits::delegation::{
    bigint_with_control::*, blake2_g_function::*, blake2_round_with_extended_control::*,
    keccak_chi5::*, keccak_column_parity::*, keccak_special5::*, keccak_theta_rho::*,
};
use crate::gkr_compiler::{GKRCircuitArtifact, GKRCompiler};
use common_constants::TIMESTAMP_COLUMNS_NUM_BITS;
use field::baby_bear::base::BabyBearField as F;
use field::{Field, PrimeField};

type Build = fn(&mut BasicAssembly<F>);

fn compile(tables: Build, circuit: Build, alignment_log2: Option<u32>) -> GKRCircuitArtifact<F> {
    let mut cs = BasicAssembly::<F>::new();
    tables(&mut cs);
    circuit(&mut cs);
    let (mut output, _) = cs.finalize();
    assert!(output
        .register_and_indirect_memory_accesses
        .iter()
        .any(|r| r.indirects_alignment_log2 != 0));
    if let Some(alignment_log2) = alignment_log2 {
        for r in output.register_and_indirect_memory_accesses.iter_mut() {
            if r.indirects_alignment_log2 != 0 {
                r.indirects_alignment_log2 = alignment_log2;
            }
        }
    }
    GKRCompiler::default().compile_delegation_circuit(output, 22, true)
}

fn delegation_circuits() -> [(&'static str, Build, Build); 7] {
    [
        (
            "bigint_with_control",
            |cs| bigint_with_extended_control_delegation_circuit_table_addition_fn(cs),
            |cs| {
                let _ = define_bigint_with_extended_control_delegation_circuit(cs);
            },
        ),
        (
            "blake2_with_compression",
            |cs| blake2_with_extended_control_table_addition_fn(cs),
            |cs| {
                let _ = define_blake2_with_extended_control_delegation_circuit(cs);
            },
        ),
        (
            "blake2_g_function",
            |cs| blake2_g_function_table_addition_fn(cs),
            |cs| {
                let _ = define_blake2_g_function_delegation_circuit(cs);
            },
        ),
        (
            "keccak_special5",
            |cs| keccak_special5_delegation_circuit_table_addition_fn(cs),
            |cs| {
                let _ = define_keccak_special5_delegation_circuit::<_, _, false>(cs);
            },
        ),
        (
            "keccak_column_parity",
            |cs| keccak_column_parity_delegation_circuit_table_addition_fn(cs),
            |cs| define_keccak_column_parity_delegation_circuit(cs),
        ),
        (
            "keccak_theta_rho",
            |cs| keccak_theta_rho_delegation_circuit_table_addition_fn(cs),
            |cs| define_keccak_theta_rho_delegation_circuit(cs),
        ),
        (
            "keccak_chi5",
            |cs| keccak_chi5_delegation_circuit_table_addition_fn(cs),
            |cs| define_keccak_chi5_delegation_circuit(cs),
        ),
    ]
}

#[test]
fn indirect_alignment_is_a_timestamp_range_check() {
    for (name, tables, circuit) in delegation_circuits() {
        let mut cs = BasicAssembly::<F>::new();
        tables(&mut cs);
        circuit(&mut cs);
        let aligned_registers = cs
            .finalize()
            .0
            .register_and_indirect_memory_accesses
            .iter()
            .filter(|r| r.indirects_alignment_log2 != 0)
            .count();
        let declared = compile(tables, circuit, None);
        let unaligned = compile(tables, circuit, Some(0));
        assert_eq!(
            declared.range_check_16_lookup_expressions.len(),
            unaligned.range_check_16_lookup_expressions.len(),
            "{name}"
        );
        assert_eq!(
            declared.timestamp_range_check_lookup_expressions.len(),
            unaligned.timestamp_range_check_lookup_expressions.len() + aligned_registers,
            "{name}"
        );
    }
}

#[test]
#[should_panic(expected = "is too large for the 19-bit timestamp range check")]
fn indirect_alignment_beyond_the_timestamp_range_check_bound_is_rejected() {
    let (_, tables, circuit) = delegation_circuits()[5];
    compile(tables, circuit, Some(12));
}

#[test]
fn timestamp_range_check_of_the_shifted_pointer_checks_alignment_exactly_below_the_bound() {
    for alignment_log2 in 1..16u32 {
        let fits =
            (1u128 << (alignment_log2 + TIMESTAMP_COLUMNS_NUM_BITS)) < F::CHARACTERISTICS_U128;
        assert_eq!(fits, alignment_log2 <= 11);
        let shift = F::from_u32_unchecked(1 << alignment_log2)
            .inverse()
            .unwrap();
        let mut wrong = 0;
        for pointer in 0..1u32 << 16 {
            let mut shifted = F::from_u32_unchecked(pointer);
            shifted.mul_assign(&shift);
            let passes = shifted.as_u32_reduced() < 1 << TIMESTAMP_COLUMNS_NUM_BITS;
            wrong += (passes != (pointer % (1 << alignment_log2) == 0)) as u32;
        }
        assert_eq!(wrong == 0, fits, "alignment 2^{alignment_log2}");
    }
}
