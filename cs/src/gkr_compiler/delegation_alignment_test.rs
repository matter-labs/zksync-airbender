use crate::cs::circuit_impl::BasicAssembly;
use crate::cs::circuit_trait::Circuit;
use crate::gkr_circuits::delegation::{
    bigint_with_control::*, blake2_g_function::*, blake2_round_with_extended_control::*,
    keccak_special5::*,
};
use crate::gkr_compiler::GKRCompiler;
use field::baby_bear::base::BabyBearField as F;

type Build = fn(&mut BasicAssembly<F>);

fn compile(tables: Build, circuit: Build, zero_alignment: bool) -> serde_json::Value {
    let mut cs = BasicAssembly::<F>::new();
    tables(&mut cs);
    circuit(&mut cs);
    let (mut output, _) = cs.finalize();
    assert!(output
        .register_and_indirect_memory_accesses
        .iter()
        .any(|r| r.indirects_alignment_log2 != 0));
    if zero_alignment {
        for r in output.register_and_indirect_memory_accesses.iter_mut() {
            r.indirects_alignment_log2 = 0;
        }
    }
    let artifact = GKRCompiler::default().compile_delegation_circuit(output, 22, true);
    serde_json::to_value(&artifact).unwrap()
}

#[test]
fn declared_indirect_alignment_is_compiled_into_delegation_circuits() {
    let circuits: [(&str, Build, Build); 4] = [
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
    ];
    for (name, tables, circuit) in circuits {
        assert_ne!(
            compile(tables, circuit, false),
            compile(tables, circuit, true),
            "{name}: the declared indirect alignment is not compiled into the circuit"
        );
    }
}
