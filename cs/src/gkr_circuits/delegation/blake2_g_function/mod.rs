use super::*;
use crate::cs::circuit::*;
use crate::cs::utils::collapse_max_quadratic_expr_into;
use crate::gkr_circuits::LookupInput;
use crate::gkr_circuits::Variable;
use crate::structured_expr::Expr;
use crate::types::Num;
use crate::witness_placer::*;
use common_constants::delegation_types::blake2s_g_function::*;

const TOTAL_TABLE_WIDTH: usize =
    1 + 1 + BLAKE2S_G_FUNCTION_X10_NUM_WRITES + BLAKE2S_G_FUNCTION_X11_NUM_READS;

// ABI:
// - registers x10-x12 are used to pass the parameters
// - x10 and x11 are pointers: x10 is a pointer to 16 words of extended state (aligned at 64 bytes), x11 is a pointer to the input to mix (aligned at 64 bytes)
// - x12 is a control register, with lower bits starting from 0 if full blake absorbtion round is needed. One bit marks if we are running reduced or not rounds,
// but such bit is only needed for witness gen for now and doesn't affect selection of inputs

pub fn all_table_types() -> Vec<TableType> {
    vec![
        TableType::Xor,
        TableType::Xor3,
        TableType::Xor4,
        TableType::Xor7,
        TableType::Xor9,
        TableType::BlakeGFunctionControlLookup,
    ]
}

pub fn blake2_g_function_delegation_circuit_create_table_driver<F: PrimeField>() -> TableDriver<F> {
    let mut table_driver = TableDriver::new();
    blake2_g_function_table_driver_fn(&mut table_driver);

    table_driver
}

pub fn blake2_g_function_table_addition_fn<F: PrimeField, CS: Circuit<F>>(cs: &mut CS) {
    for el in all_table_types() {
        cs.materialize_table::<TOTAL_TABLE_WIDTH>(el);
    }
}

pub fn blake2_g_function_table_driver_fn<F: PrimeField>(table_driver: &mut TableDriver<F>) {
    for el in all_table_types() {
        table_driver.materialize_table::<TOTAL_TABLE_WIDTH>(el);
    }
}

fn chunks_expr<F: PrimeField>(chunks: impl IntoIterator<Item = (usize, Variable)>) -> Expr<F> {
    let mut expr = Expr::<F>::zero();
    let mut shift = 0;
    for (width, var) in chunks {
        expr = expr + Expr::var(var) * F::from_u32_unchecked(1u32 << shift);
        shift += width;
    }

    expr
}

pub fn define_blake2_g_function_delegation_circuit<F: PrimeField, CS: Circuit<F>>(
    cs: &mut CS,
) -> [[Variable; 2]; BLAKE2S_G_FUNCTION_X10_NUM_WRITES] {
    let (execute, _invocation_timestamp) =
        cs.allocate_delegation_state(BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER as u16);

    // we do not expect any variable offsets, so we allocate all register and indirect reads/writes right away

    let x12_request = RegisterAccessRequest {
        register_index: 12,
        register_write: true,
        indirects_alignment_log2: 0, // no indirects
        indirect_accesses: vec![],
    };

    let x12_and_indirects = cs.request_register_and_indirect_memory_accesses(
        x12_request,
        "control read/write from x12",
        2,
    );

    let (x12_vars, x12_write_vars) = {
        let RegisterAccessType::Write {
            read_value,
            write_value,
        } = x12_and_indirects.register_access
        else {
            panic!()
        };

        (read_value, write_value)
    };

    // higher 16 bits of both read and write values are 0s

    // set value for low bits and constraint it
    let value_fn = move |placer: &mut CS::WitnessPlacer| {
        let zero = <CS::WitnessPlacer as WitnessTypeSet<F>>::U16::constant(0);
        placer.assign_u16(x12_write_vars[1], &zero);
    };
    cs.set_values(value_fn);
    cs.add_constraint_expr_allow_explicit_linear_prevent_optimizations_expr(Expr::var(x12_vars[1]));
    cs.add_constraint_expr_allow_explicit_linear_prevent_optimizations_expr(Expr::var(
        x12_write_vars[1],
    ));

    // we will validate the control register value, make a "next one",
    // and also produce indexes for
    let [x10_offset_0, x10_offset_1, x10_offset_2, x_10_offset_3] =
        std::array::from_fn(|i| cs.add_named_variable(&format!("x10 offset {}", i)));
    let [x11_offset_0, x_11_offset_1] =
        std::array::from_fn(|i| cs.add_named_variable(&format!("x11 offset {}", i)));

    // note: for simplicity - our logical input also includes execute flag, so we just degrade to 0 in padding
    let input_expr = Expr::<F>::var(x12_vars[0])
        + Expr::var(execute)
            * F::from_u32_unchecked(1 << BLAKE2S_G_FUNCTION_NUM_CONTROL_REGISTER_BITS);
    if CS::ASSUME_MEMORY_VALUES_ASSIGNED {
        let mut inputs = vec![LookupInput::from(input_expr.clone())];
        inputs.extend(
            [
                x12_write_vars[0],
                x10_offset_0,
                x10_offset_1,
                x10_offset_2,
                x_10_offset_3,
                x11_offset_0,
                x_11_offset_1,
            ]
            .map(|el| LookupInput::Variable(el)),
        );
        let inputs: [_; TOTAL_TABLE_WIDTH] = inputs.try_into().unwrap();
        cs.enforce_lookup_tuple_for_fixed_table(
            &inputs.map(|el| LookupInput::from(el)),
            TableType::BlakeGFunctionControlLookup,
            false,
        );
    } else {
        cs.set_variables_from_lookup_constrained(
            &[LookupInput::from(input_expr)],
            &[
                x12_write_vars[0],
                x10_offset_0,
                x10_offset_1,
                x10_offset_2,
                x_10_offset_3,
                x11_offset_0,
                x_11_offset_1,
            ],
            LookupQueryTableType::Constant(TableType::BlakeGFunctionControlLookup),
        );
    }

    // NOTE: offsets are in words
    let x10_offsets = [x10_offset_0, x10_offset_1, x10_offset_2, x_10_offset_3];
    let x11_offsets = [x11_offset_0, x_11_offset_1];

    let state_accesses = (0..BLAKE2S_G_FUNCTION_X10_NUM_WRITES)
        .into_iter()
        .map(|access_idx| IndirectAccessOffset {
            variable_dependent: Some((core::mem::size_of::<u32>() as u32, x10_offsets[access_idx])),
            offset_constant: 0,
            assume_no_alignment_overflow: true,
            is_write_access: true,
        })
        .collect();

    let x10_request = RegisterAccessRequest {
        register_index: 10,
        register_write: false,
        indirects_alignment_log2: 6, // just aligned by machine words of the full extended state
        indirect_accesses: state_accesses,
    };

    let input_accesses = (0..BLAKE2S_G_FUNCTION_X11_NUM_READS)
        .into_iter()
        .map(|access_idx| IndirectAccessOffset {
            variable_dependent: Some((core::mem::size_of::<u32>() as u32, x11_offsets[access_idx])),
            offset_constant: 0,
            assume_no_alignment_overflow: true,
            is_write_access: false,
        })
        .collect();

    let x11_request = RegisterAccessRequest {
        register_index: 11,
        register_write: false,
        indirects_alignment_log2: 6, // just aligned by machine words of the full input
        indirect_accesses: input_accesses,
    };

    let x10_and_indirects = cs.request_register_and_indirect_memory_accesses(
        x10_request,
        "state read/write from x10",
        2,
    );
    let x11_and_indirects =
        cs.request_register_and_indirect_memory_accesses(x11_request, "input read from x11", 2);

    assert_eq!(
        x10_and_indirects.indirect_accesses.len(),
        BLAKE2S_G_FUNCTION_X10_NUM_WRITES
    );
    assert_eq!(
        x11_and_indirects.indirect_accesses.len(),
        BLAKE2S_G_FUNCTION_X11_NUM_READS
    );
    assert!(x12_and_indirects.indirect_accesses.is_empty());

    let mut input_extended_state_reads = vec![];
    let mut output_placeholder_extended_state = vec![];
    for i in 0..BLAKE2S_G_FUNCTION_X10_NUM_WRITES {
        let IndirectAccessType::Write {
            read_value,
            write_value,
            ..
        } = x10_and_indirects.indirect_accesses[i]
        else {
            panic!()
        };

        input_extended_state_reads.push(read_value);
        output_placeholder_extended_state.push(write_value);
    }
    let mut output_placeholder_extended_state: [[Variable; 2]; BLAKE2S_G_FUNCTION_X10_NUM_WRITES] =
        output_placeholder_extended_state.try_into().unwrap();

    let mut input_words_reads = vec![];
    for i in 0..BLAKE2S_G_FUNCTION_X11_NUM_READS {
        let IndirectAccessType::Read { read_value, .. } = x11_and_indirects.indirect_accesses[i]
        else {
            panic!()
        };

        input_words_reads.push(read_value);
    }

    {
        for (i, input) in input_extended_state_reads.iter().enumerate() {
            let register = Register::<F>(input.map(|el| Num::Var(el)));
            if let Some(value) = register.get_value_unsigned(&*cs) {
                println!("Input state element {} = 0x{:08x}", i, value);
            }
        }

        for (i, input) in input_words_reads.iter().enumerate() {
            let register = Register::<F>(input.map(|el| Num::Var(el)));
            if let Some(value) = register.get_value_unsigned(&*cs) {
                println!("Input extended state element {} = 0x{:08x}", i, value);
            }
        }

        let register = Register::<F>(x12_vars.map(|el| Num::Var(el)));
        if let Some(value) = register.get_value_unsigned(&*cs) {
            println!("Control register = 0b{:b}", value);
        }
    }

    // NOTE: G function structure is
    // v[a] = v[a].wrapping_add(v[b]).wrapping_add(x);
    // v[d] = rotate_right::<16>(v[d] ^ v[a]);
    // v[c] = v[c].wrapping_add(v[d]);
    // v[b] = rotate_right::<12>(v[b] ^ v[c]);
    // v[a] = v[a].wrapping_add(v[b]).wrapping_add(y);
    // v[d] = rotate_right::<8>(v[d] ^ v[a]);
    // v[c] = v[c].wrapping_add(v[d]);
    // v[b] = rotate_right::<7>(v[b] ^ v[c]);

    // and we already selected v[a]/v[b]/v[c]/v[d] and x/y words. We just need to run it and dump outputs

    let state: Vec<_> = input_extended_state_reads
        .iter()
        .map(|el| el.map(|el| vec![(16, el)]))
        .collect();

    let a_row: [_; 1] = [state[0].clone()];
    let mut a_row = a_row.map(|el| {
        el.map(|el| {
            assert_eq!(el.len(), 1);
            Expr::<F>::var(el[0].1)
        })
    });
    let mut b_row: [_; 1] = [state[1].clone()];
    let c_row: [_; 1] = [state[2].clone()];
    let mut c_row = c_row.map(|el| {
        el.map(|el| {
            assert_eq!(el.len(), 1);
            Expr::<F>::var(el[0].1)
        })
    });
    let mut d_row: [_; 1] = [state[3].clone()];

    // perform actual mixing
    use crate::gkr_circuits::blake2_round_with_extended_control::g_function;

    // we do not need output decomposition, as we will not XOR again with anything as we do in blake round function.

    // G function structure is
    // v[a] = v[a].wrapping_add(v[b]).wrapping_add(x);
    // v[d] = rotate_right::<16>(v[d] ^ v[a]);
    // v[c] = v[c].wrapping_add(v[d]);
    // v[b] = rotate_right::<12>(v[b] ^ v[c]);
    // v[a] = v[a].wrapping_add(v[b]).wrapping_add(y);
    // v[d] = rotate_right::<8>(v[d] ^ v[a]);
    // v[c] = v[c].wrapping_add(v[d]);
    // v[b] = rotate_right::<7>(v[b] ^ v[c]);

    // and in our implementation even though we chunk `a` and `c` using extra witness, they are immediatelly fed into XOR + rotate lookups,
    // so `a`/`c` chunks and constraints are range checked

    let _output_decompositions = g_function::g_function(
        cs,
        &mut a_row[0],
        &mut b_row[0],
        &mut c_row[0],
        &mut d_row[0],
        [input_words_reads[0], input_words_reads[1]],
    );

    // now we should re-assemble it into output

    // NOTE: even though we output `a` and `c` rows, they are the result of addition and

    // we unconditionally set values for extended state
    {
        let mut it = output_placeholder_extended_state.iter_mut();

        for src in a_row.into_iter() {
            let dst = it.next().unwrap();
            for (src, dst) in src.into_iter().zip(dst.iter_mut()) {
                let expr = src;
                collapse_max_quadratic_expr_into(cs, expr.clone(), *dst);
                cs.define_variable_from_expr(*dst, expr);
            }
        }

        for src in b_row.iter().cloned() {
            let dst = it.next().unwrap();
            for (src, dst) in src.into_iter().zip(dst.iter_mut()) {
                let expr = chunks_expr(src);
                collapse_max_quadratic_expr_into(cs, expr.clone(), *dst);
                cs.define_variable_from_expr(*dst, expr);
            }
        }

        for src in c_row.into_iter() {
            let dst = it.next().unwrap();
            for (src, dst) in src.into_iter().zip(dst.iter_mut()) {
                let expr = src;
                collapse_max_quadratic_expr_into(cs, expr.clone(), *dst);
                cs.define_variable_from_expr(*dst, expr);
            }
        }

        for src in d_row.iter().cloned() {
            let dst = it.next().unwrap();
            for (src, dst) in src.into_iter().zip(dst.iter_mut()) {
                let expr = chunks_expr(src);
                collapse_max_quadratic_expr_into(cs, expr.clone(), *dst);
                cs.define_variable_from_expr(*dst, expr);
            }
        }
        assert!(it.next().is_none());
    }

    {
        for (i, input) in output_placeholder_extended_state.iter().enumerate() {
            let register = Register::<F>(input.map(|el| Num::Var(el)));
            if let Some(value) = register.get_value_unsigned(&*cs) {
                println!("Output extended state element {} = 0x{:08x}", i, value);
            }
        }
    }

    output_placeholder_extended_state
}

#[cfg(test)]
mod test {
    use test_utils::skip_if_ci;

    use super::*;
    use crate::cs::circuit_impl::BasicAssembly;
    use crate::gkr_compiler::compile_delegation_circuit_into_gkr;
    use crate::gkr_compiler::compile_delegation_circuit_into_gkr_without_caches;
    use crate::gkr_compiler::dump_ssa_witness_eval_form;
    use crate::structured_expr::StructuredStatement;
    use crate::utils::serialize_to_file;
    use field::Field;

    type F = ::field::Mersenne31Field;

    // fn is_scaled_variable(expr: &Expr<F>) -> bool {
    //     let Expr::Product(factors) = expr else {
    //         return false;
    //     };

    //     factors.iter().any(|factor| matches!(factor, Expr::Var(_)))
    //         && factors
    //             .iter()
    //             .any(|factor| matches!(factor, Expr::Constant(value) if *value != F::ZERO && *value != F::ONE))
    // }

    // fn is_linear_chunk_composition(expr: &Expr<F>) -> bool {
    //     let Expr::Sum(terms) = expr else {
    //         return false;
    //     };

    //     terms.iter().any(|term| matches!(term, Expr::Var(_)))
    //         && terms.iter().any(is_scaled_variable)
    // }

    // #[test]
    // fn blake2_g_function_records_structured_output_reassembly() {
    //     let mut cs = BasicAssembly::<F>::new();
    //     let _ = define_blake2_g_function_delegation_circuit(&mut cs);
    //     let (output, _) = cs.finalize();

    //     let high_zero_assertions = output
    //         .structured_statements
    //         .iter()
    //         .filter(|statement| {
    //             matches!(
    //                 statement,
    //                 StructuredStatement::AssertZero {
    //                     expr: Expr::Var(_),
    //                     prevent_optimizations: true,
    //                 }
    //             )
    //         })
    //         .count();

    //     let reassembled_outputs = output
    //         .structured_statements
    //         .iter()
    //         .filter(|statement| {
    //             matches!(
    //                 statement,
    //                 StructuredStatement::Define { expr, .. } if is_linear_chunk_composition(expr)
    //             )
    //         })
    //         .count();

    //     assert!(high_zero_assertions >= 2);
    //     assert!(reassembled_outputs >= 2);
    // }

    #[test]
    fn compile_blake2_g_function_into_gkr() {
        skip_if_ci!();
        use ::field::baby_bear::base::BabyBearField;

        let gkr_compiled = compile_delegation_circuit_into_gkr::<BabyBearField>(
            &|cs| blake2_g_function_table_addition_fn(cs),
            &|cs| {
                let _ = define_blake2_g_function_delegation_circuit(cs);
            },
            22,
        );

        serialize_to_file(
            &gkr_compiled,
            "compiled_circuits/blake2_g_function_layout_gkr.json",
        );
    }

    #[test]
    fn compile_blake2_g_function_witness_graph() {
        skip_if_ci!();
        use ::field::baby_bear::base::BabyBearField;

        let ssa_forms = dump_ssa_witness_eval_form::<BabyBearField>(
            &|cs| blake2_g_function_table_addition_fn(cs),
            &|cs| {
                let _ = define_blake2_g_function_delegation_circuit(cs);
            },
        );
        serialize_to_file(
            &ssa_forms,
            "compiled_circuits/blake2_g_function_ssa_gkr.json",
        );
    }

    #[test]
    fn compile_blake2_g_function_into_no_caches_gkr() {
        skip_if_ci!();
        use ::field::baby_bear::base::BabyBearField;

        let gkr_compiled = compile_delegation_circuit_into_gkr_without_caches::<BabyBearField>(
            &|cs| blake2_g_function_table_addition_fn(cs),
            &|cs| {
                let _ = define_blake2_g_function_delegation_circuit(cs);
            },
            22,
        );

        serialize_to_file(
            &gkr_compiled,
            "compiled_circuits/blake2_g_function_layout_no_caches_gkr.json",
        );
    }

    /// Fixture generator (run explicitly): emit the lowered codegen-IR JSON in
    /// both the caching and no-caching variants. Run with:
    ///
    ///   cargo test -p cs generate_blake2_g_function_codegen_ir_json -- --ignored --nocapture
    #[test]
    #[ignore]
    fn generate_blake2_g_function_codegen_ir_json() {
        use ::field::baby_bear::base::BabyBearField;
        use crate::gkr_compiler::write_codegen_ir_fixture;

        let cached = compile_delegation_circuit_into_gkr::<BabyBearField>(
            &|cs| blake2_g_function_table_addition_fn(cs),
            &|cs| {
                let _ = define_blake2_g_function_delegation_circuit(cs);
            },
            22,
        );
        write_codegen_ir_fixture(
            &cached,
            "compiled_circuits/blake2_g_function_codegen_ir_gkr.json",
        );

        let no_caches = compile_delegation_circuit_into_gkr_without_caches::<BabyBearField>(
            &|cs| blake2_g_function_table_addition_fn(cs),
            &|cs| {
                let _ = define_blake2_g_function_delegation_circuit(cs);
            },
            22,
        );
        write_codegen_ir_fixture(
            &no_caches,
            "compiled_circuits/blake2_g_function_codegen_ir_no_caches_gkr.json",
        );
    }
}
