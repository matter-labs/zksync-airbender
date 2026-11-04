//! Capture source arithmetic before compiling, together with the actual GKR output.
//!
//! Usage: export_gkr_translation FAMILY OUTPUT.json [--cached]
//! The arithmetic snapshot is independent of the compiler's post-lowering
//! constraint summaries. Counts explicitly identify the remaining source inputs;
//! this export does not yet certify lookup or memory lowering.

use cs::cs::{circuit_impl::BasicAssembly, circuit_trait::Circuit};
use cs::gkr_circuits::delegation::{bigint_with_control, keccak_special5};
use cs::gkr_circuits::*;
use cs::gkr_compiler::GKRCompiler;
use field::baby_bear::base::BabyBearField as F;
use serde_json::json;
use std::path::Path;

type Build = fn(&mut BasicAssembly<F>);

fn write_json_if_changed(path: &Path, value: &serde_json::Value) -> std::io::Result<()> {
    let mut bytes = serde_json::to_vec(value)?;
    bytes.push(b'\n');
    if std::fs::read(path).ok().as_deref() != Some(bytes.as_slice()) {
        std::fs::write(path, bytes)?;
    }
    Ok(())
}

fn builders(family: &str) -> Result<(Build, Build, bool), &'static str> {
    Ok(match family {
        "add-sub" => (
            add_sub_lui_auipc_mop_table_addition_fn,
            add_sub_lui_auipc_mop_circuit_with_preprocessed_bytecode_for_gkr,
            false,
        ),
        "jump-branch" => (
            jump_branch_slt_table_addition_fn,
            jump_branch_slt_circuit_with_preprocessed_bytecode_for_gkr,
            false,
        ),
        "mul-div" => (
            mul_div_table_addition_fn::<F, _, false>,
            mul_div_circuit_with_preprocessed_bytecode_for_gkr::<F, _, false>,
            false,
        ),
        "shift-binop" => (
            shift_binop_table_addition_fn,
            shift_binop_circuit_with_preprocessed_bytecode_for_gkr,
            false,
        ),
        "word-memory" => (
            mem_word_only_table_addition_fn,
            mem_word_only_circuit_with_preprocessed_bytecode_for_gkr,
            false,
        ),
        "subword-memory" => (
            mem_subword_only_table_addition_fn,
            mem_subword_only_circuit_with_preprocessed_bytecode_for_gkr,
            false,
        ),
        "unified" => (
            unified_reduced_machine_table_addition_fn,
            unified_reduced_machine_circuit_with_preprocessed_bytecode_for_gkr,
            false,
        ),
        "bigint" => (
            bigint_with_control::bigint_with_extended_control_delegation_circuit_table_addition_fn,
            |cs| {
                bigint_with_control::define_bigint_with_extended_control_delegation_circuit(cs);
            },
            true,
        ),
        "blake-g" => (
            blake2_g_function::blake2_g_function_table_addition_fn,
            |cs| {
                blake2_g_function::define_blake2_g_function_delegation_circuit(cs);
            },
            true,
        ),
        "blake-round" => (
            blake2_round_with_extended_control::blake2_with_extended_control_table_addition_fn,
            |cs| {
                blake2_round_with_extended_control::define_blake2_with_extended_control_delegation_circuit(cs);
            },
            true,
        ),
        "keccak" => (
            keccak_special5::keccak_special5_delegation_circuit_table_addition_fn,
            |cs| keccak_special5::define_keccak_special5_delegation_circuit::<_, _, false>(cs),
            true,
        ),
        _ => return Err("unsupported production circuit family"),
    })
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if !(args.len() == 2 || (args.len() == 3 && args[2] == "--cached")) {
        return Err("usage: export_gkr_translation FAMILY OUTPUT.json [--cached]".into());
    }
    let cached = args.len() == 3;
    let (tables, build, delegation) = builders(&args[0])?;
    let mut assembly = BasicAssembly::<F>::new();
    tables(&mut assembly);
    // Match the production builders' physical ROM table registration, even
    // though the audited source arithmetic is independent of program bytes.
    if args[0] == "word-memory" || args[0] == "unified" {
        for (kind, table) in create_mem_word_only_special_tables::<
            F,
            { common_constants::ROM_SECOND_WORD_BITS },
        >(&[])
        {
            assembly.add_table_with_content(kind, table);
        }
    } else if args[0] == "subword-memory" {
        for (kind, table) in create_mem_subword_only_special_tables::<
            F,
            { common_constants::ROM_SECOND_WORD_BITS },
        >(&[])
        {
            assembly.add_table_with_content(kind, table);
        }
    }
    build(&mut assembly);
    let (source, _) = assembly.finalize();

    // Serialize while the original, unmodified CircuitOutput still exists.
    // The compiler consumes it only after this owned JSON value is complete.
    let mut layers: Vec<_> = source.layers_mapping.iter().collect();
    layers.sort_unstable_by_key(|(variable, _)| variable.0);
    let mut substitutions: Vec<_> = source.substitutions.iter().collect();
    substitutions.sort_unstable_by_key(|((placeholder, index), _)| (*placeholder, *index));
    let table_sizes: Vec<_> = source
        .table_driver
        .tables
        .iter()
        .map(|table| table.get_size())
        .collect();
    let semantic_inputs = json!({
        "lookups": source.lookups,
        "range_checks": source.range_check_expressions,
        "memory_queries": source.memory_queries,
        "register_and_indirect_accesses": source.register_and_indirect_memory_accesses,
        "read_timestamp_group_distances": source.read_timestamp_group_distances,
        "executor_machine_state": source.executor_machine_state,
        "delegation_circuit_state": source.delegation_circuit_state,
        "circuit_family_bitmask": source.circuit_family_bitmask,
        "variables_from_constraints": source.variables_from_constraints,
        "substitutions": substitutions,
        "variable_names": source.variable_names,
        "table_sizes": table_sizes,
        "total_tables_len": source.table_driver.total_tables_len,
    });
    let source_snapshot = json!({
        "num_variables": source.num_of_variables,
        "statements": source.structured_statements,
        "booleans": source.boolean_vars,
        "layers": layers,
        "remaining_inputs": {
            "lookups": source.lookups.len(),
            "range_checks": source.range_check_expressions.len(),
            "memory_queries": source.memory_queries.len(),
            "register_and_indirect_accesses": source.register_and_indirect_memory_accesses.len(),
            "executor": source.executor_machine_state.is_some(),
            "delegation": source.delegation_circuit_state.is_some(),
        },
    });
    let compiler = GKRCompiler::default();
    let trace_log2 = match args[0].as_str() {
        "mul-div" | "unified" => 23,
        "bigint" | "blake-g" | "keccak" => 22,
        "blake-round" => 20,
        _ => 24,
    };
    let circuit = if delegation {
        compiler.compile_delegation_circuit(source, trace_log2, cached)
    } else if args[0] == "unified" {
        compiler.compile_family_circuit_with_inline_inits_and_teardowns(
            source,
            common_constants::ROM_WORD_SIZE,
            1,
            trace_log2,
            cached,
        )
    } else {
        compiler.compile_family_circuit(
            source,
            common_constants::ROM_WORD_SIZE,
            0,
            trace_log2,
            cached,
        )
    };
    let artifact = json!({
        "format_version": 1,
        "family": args[0],
        "cached": cached,
        "source": source_snapshot,
        "circuit": circuit,
    });
    let output = Path::new(&args[1]);
    let sidecar = output.with_file_name(format!(
        "{}-source.json",
        output
            .file_stem()
            .ok_or("missing output name")?
            .to_string_lossy()
    ));
    let complete_source = json!({
        "format_version": 1,
        "family": args[0],
        "cached": cached,
        "source": source_snapshot,
        "semantic_inputs": semantic_inputs,
        "configuration": {
            "trace_len_log2": trace_log2,
            "max_bytecode_size_in_words": if delegation { 0 } else { common_constants::ROM_WORD_SIZE },
            "inline_init_teardown_pairs": usize::from(args[0] == "unified"),
        },
    });
    write_json_if_changed(output, &artifact)?;
    write_json_if_changed(&sidecar, &complete_source)?;
    println!(
        "Wrote source/compiler pair and complete source sidecar to {}",
        args[1]
    );
    Ok(())
}
