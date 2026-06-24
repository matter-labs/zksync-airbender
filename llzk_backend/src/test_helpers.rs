//! Shared helpers for LLZK backend unit tests.

use std::collections::HashMap;
use std::env;

use anyhow::Result;
use llzk::prelude::*;
use melior::ir::operation::OperationLike;
use melior::ir::operation::OperationPrintingFlags;
use prover::cs::definitions::Variable;
use prover::field::Mersenne31Field;

use crate::builder::ModuleEnv;
use crate::builder::OpsBuilder;
use crate::builder::StructBuilder;
use crate::codegen::SpecialCsrPropertiesMetadata;
use crate::codegen::StructVars;
use crate::config::DebugLocationStyle;
use crate::constraints::AddConstraints;

/// Normalize textual IR by trimming trailing whitespace at the end of each line.
///
/// The textual IR printer currently emits a few trailing spaces, so tests
/// compare normalized strings rather than relying on editor-specific whitespace handling.
fn normalize_ir(ir: &str) -> String {
    ir.trim()
        .lines()
        .map(str::trim_end)
        .collect::<Vec<_>>()
        .join("\n")
}

/// Assert that two IR strings are exactly equal after normalization.
pub(crate) fn assert_full_ir_eq(actual: &str, expected: &str) {
    assert_eq!(normalize_ir(actual), normalize_ir(expected));
}

/// Dump test IR to stdout when `LLZK_DUMP_TEST_IR` is set.
pub(crate) fn maybe_dump_test_ir(name: &str, ir: &str) {
    if env::var_os("LLZK_DUMP_TEST_IR").is_some() {
        println!("=== {name} ===");
        println!("{ir}");
        println!("=== end {name} ===");
    }
}

/// Emit a synthetic `@constrain` body for unit tests.
///
/// The helper exposes each `input_var` as a felt input, each `member_var` as a felt
/// struct member, and then runs `emit` inside the generated `@constrain` body.
pub(crate) fn emit_test_constrain_ir(
    struct_name: &str,
    input_vars: &[Variable],
    member_vars: &[(Variable, &str)],
    emit: impl FnOnce(&OpsBuilder<'_, '_, Mersenne31Field>, &StructVars<Mersenne31Field>) -> Result<()>,
) -> String {
    emit_test_constrain_ir_with_special_csr_properties(
        struct_name,
        input_vars,
        member_vars,
        None,
        emit,
    )
}

/// Emit a synthetic `@constrain` body for unit tests, optionally seeding
/// `SpecialCSRProperties` metadata on the synthetic [`StructVars`].
pub(crate) fn emit_test_constrain_ir_with_special_csr_properties(
    struct_name: &str,
    input_vars: &[Variable],
    member_vars: &[(Variable, &str)],
    special_csr_properties: Option<SpecialCsrPropertiesMetadata>,
    emit: impl FnOnce(&OpsBuilder<'_, '_, Mersenne31Field>, &StructVars<Mersenne31Field>) -> Result<()>,
) -> String {
    let ctx = LlzkContext::new();
    let module = llzk_module(Location::unknown(&ctx));
    let env = ModuleEnv::<Mersenne31Field>::new(&ctx, &module, DebugLocationStyle::Named);

    let mut struct_builder = StructBuilder::new(&env, struct_name);
    for _ in input_vars {
        struct_builder.with_input_location(env.felt_type(), Location::unknown(&ctx));
    }
    for (_, name) in member_vars {
        struct_builder.with_member_location(
            (*name).to_string(),
            env.felt_type(),
            false,
            Location::unknown(&ctx),
        );
    }

    let arg_map = input_vars
        .iter()
        .enumerate()
        .map(|(idx, var)| (*var, (idx, None)))
        .collect::<HashMap<_, _>>();
    let member_map = member_vars
        .iter()
        .map(|(var, name)| (*var, ((*name).to_string(), None)))
        .collect::<HashMap<_, _>>();
    let vars = StructVars::from_test_maps_with_special_csr_properties(
        member_map,
        arg_map,
        special_csr_properties,
    );

    let struct_op = struct_builder.build_in_module().unwrap();
    struct_op
        .add_constraints(&env, |ops| emit(ops, &vars))
        .unwrap();
    verify_operation_with_diags(&module.as_operation()).unwrap();

    format!("{}", module.as_operation())
}

/// Emit a synthetic `@constrain` body for unit tests and serialize it with MLIR debug info
/// enabled so semantic locations appear in the textual IR.
pub(crate) fn emit_test_constrain_ir_with_debug_info(
    struct_name: &str,
    input_vars: &[Variable],
    member_vars: &[(Variable, &str)],
    emit: impl FnOnce(&OpsBuilder<'_, '_, Mersenne31Field>, &StructVars<Mersenne31Field>) -> Result<()>,
) -> String {
    let ctx = LlzkContext::new();
    let module = llzk_module(Location::unknown(&ctx));
    let env = ModuleEnv::<Mersenne31Field>::new(&ctx, &module, DebugLocationStyle::Named);

    let mut struct_builder = StructBuilder::new(&env, struct_name);
    for _ in input_vars {
        struct_builder.with_input_location(env.felt_type(), Location::unknown(&ctx));
    }
    for (_, name) in member_vars {
        struct_builder.with_member_location(
            (*name).to_string(),
            env.felt_type(),
            false,
            Location::unknown(&ctx),
        );
    }

    let arg_map = input_vars
        .iter()
        .enumerate()
        .map(|(idx, var)| (*var, (idx, None)))
        .collect::<HashMap<_, _>>();
    let member_map = member_vars
        .iter()
        .map(|(var, name)| (*var, ((*name).to_string(), None)))
        .collect::<HashMap<_, _>>();
    let vars = StructVars::from_test_maps_with_special_csr_properties(member_map, arg_map, None);

    let struct_op = struct_builder.build_in_module().unwrap();
    struct_op
        .add_constraints(&env, |ops| emit(ops, &vars))
        .unwrap();
    verify_operation_with_diags(&module.as_operation()).unwrap();

    module
        .as_operation()
        .to_string_with_flags(OperationPrintingFlags::new().enable_debug_info(true, false))
        .map(|ir| {
            maybe_dump_test_ir(struct_name, &ir);
            ir
        })
        .unwrap()
}
