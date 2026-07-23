use cs::definitions::{GKRAddress, Variable, VirtualSetupPoly};
use cs::gkr_compiler::GKRCircuitArtifact;
use cs::oracle::Placeholder;
use cs::witness_placer::graph_description::{
    BoolNodeExpression, Expression, FieldNodeExpression, FixedWidthIntegerNodeExpression,
    RawExpression,
};
use std::collections::{BTreeMap, BTreeSet};
use std::fs::File;
use std::path::{Path, PathBuf};

mod boolean;
mod field;
mod integer;

/// Internal column-address kind used by the generator. Upstream removed the
/// `cs::definitions::ColumnAddress` enum; we keep a local one here that the
/// generator maps `GKRAddress` into, so the SSA-walker code unchanged.
#[derive(Clone, Copy, Debug)]
pub(crate) enum ColumnAddress {
    MemorySubtree(usize),
    WitnessSubtree(usize),
    SetupSubtree(usize),
    OptimizedOut(usize),
}

pub type F = ::field::baby_bear::base::BabyBearField;

pub struct Generator {
    write_into_memory: bool,
    layout: BTreeMap<Variable, ColumnAddress>,
    num_lookup_mappings: usize,
    next_var_idx: usize,
    output: String,
    scratch_size: usize,
    fn_indexes: Vec<usize>,
    // Witness columns that are ONLY ever written under an `IF` guard (no
    // unconditional write anywhere in the graph). The generators write them
    // per-opcode, so rows whose opcode doesn't match leave the column
    // untouched. The CPU witness is lazily zero-filled, so those gaps must read
    // as zero; we fold a zero-default into each such column's FIRST write.
    conditional_only_witness: BTreeSet<usize>,
    // Conditional-only witness columns whose first write has already been
    // emitted (as `SET_WITNESS_PLACE_OR_ZERO`). Subsequent writes stay `IF`.
    witness_zero_default_emitted: BTreeSet<usize>,
}

impl Generator {
    fn new(
        layout: &BTreeMap<Variable, ColumnAddress>,
        num_lookup_mappings: usize,
        write_into_memory: bool,
    ) -> Self {
        let scratch_size = layout
            .values()
            .filter_map(|address| match address {
                ColumnAddress::OptimizedOut(idx) => Some(idx + 1),
                _ => None,
            })
            .max()
            .unwrap_or(0);
        Self {
            layout: layout.clone(),
            num_lookup_mappings,
            write_into_memory,
            next_var_idx: 0,
            output: String::new(),
            scratch_size,
            fn_indexes: Vec::new(),
            conditional_only_witness: BTreeSet::new(),
            witness_zero_default_emitted: BTreeSet::new(),
        }
    }

    /// Classify witness-column writes across the whole graph and record the
    /// columns that are written exclusively under an `IF` condition. A column
    /// with any unconditional write is fully covered and never needs a default;
    /// the partition is clean in practice (no column is both), so folding a
    /// zero-default into such a column's first write can't clobber a real write.
    fn collect_conditional_only_witness(&mut self, graph: &[Vec<RawExpression<F>>]) {
        let mut unconditional = BTreeSet::new();
        let mut conditional = BTreeSet::new();
        for expressions in graph {
            for expr in expressions {
                if let RawExpression::WriteVariable {
                    into_variable,
                    condition_subexpr_idx,
                    ..
                } = expr
                    && let ColumnAddress::WitnessSubtree(idx) =
                        self.get_column_address(into_variable)
                {
                    if condition_subexpr_idx.is_some() {
                        conditional.insert(idx);
                    } else {
                        unconditional.insert(idx);
                    }
                }
            }
        }
        self.conditional_only_witness = conditional.difference(&unconditional).copied().collect();
    }

    fn create_var(&mut self) -> usize {
        let idx = self.next_var_idx;
        self.next_var_idx += 1;
        idx
    }

    fn get_column_address(&self, variable: &Variable) -> ColumnAddress {
        if variable.is_placeholder() {
            panic!("variable is placeholder");
        }
        self.layout[variable]
    }

    fn get_placeholder_ident(placeholder: &Placeholder) -> &'static str {
        match placeholder {
            Placeholder::PcInit => "{ PcInit }",
            Placeholder::SecondRegMem => "{ SecondRegMem }",
            Placeholder::MemSlot => "{ MemSlot }",
            Placeholder::ExternalOracle => "{ ExternalOracle }",
            Placeholder::WriteRdReadSetWitness => "{ WriteRdReadSetWitness }",
            _ => unimplemented!(),
        }
    }

    fn field_expr_into_var(&self, expr: &FieldNodeExpression<F>) -> usize {
        let FieldNodeExpression::SubExpression(idx) = expr else {
            unreachable!();
        };
        *idx
    }

    fn boolean_expr_into_var(&self, expr: &BoolNodeExpression<F>) -> usize {
        let BoolNodeExpression::SubExpression(idx) = expr else {
            unreachable!();
        };
        *idx
    }

    fn integer_expr_into_var(&self, expr: &FixedWidthIntegerNodeExpression<F>) -> usize {
        match expr {
            FixedWidthIntegerNodeExpression::U8SubExpression(idx)
            | FixedWidthIntegerNodeExpression::U16SubExpression(idx)
            | FixedWidthIntegerNodeExpression::U32SubExpression(idx) => *idx,
            a => {
                panic!("Trying to make variable from expression {:?}", a);
            }
        }
    }

    fn expression_into_var(&self, expr: &Expression<F>) -> usize {
        match expr {
            Expression::Bool(expr) => self.boolean_expr_into_var(expr),
            Expression::Field(expr) => self.field_expr_into_var(expr),
            Expression::U8(expr) | Expression::U16(expr) | Expression::U32(expr) => {
                self.integer_expr_into_var(expr)
            }
        }
    }

    fn push(&mut self, string: &str) {
        self.output.push_str(string);
    }

    /// Emit a generator-macro call `MACRO([type_tag, ]new_ident, operands...)\n`,
    /// allocating and returning the fresh output variable `new_ident`. This is
    /// the shape shared by nearly every field/integer/boolean node: a handful
    /// of macros (e.g. `AND`, `NEGATE`) take no width tag, hence `Option`.
    fn emit(&mut self, macro_name: &str, type_tag: Option<&str>, operands: &[usize]) -> usize {
        let new_ident = self.create_var();
        match type_tag {
            Some(tag) => self.push(&format!("{macro_name}({tag}, {new_ident}")),
            None => self.push(&format!("{macro_name}({new_ident}")),
        }
        for operand in operands {
            self.push(&format!(", {operand}"));
        }
        self.push(")\n");
        new_ident
    }

    /// Emit the `GET_{WITNESS,MEMORY,SCRATCH}_PLACE` read dispatch shared by
    /// every `*Place` node kind (field/boolean/u8/u16), keyed by `type_tag`.
    /// `SetupSubtree` reads are intentionally unimplemented (out of scope).
    fn emit_place_read(&mut self, type_tag: &str, variable: &Variable) -> usize {
        let new_ident = self.create_var();
        let address = self.get_column_address(variable);
        match address {
            ColumnAddress::WitnessSubtree(idx) => {
                self.push(&format!(
                    "GET_WITNESS_PLACE({type_tag}, {new_ident}, {idx})\n"
                ));
            }
            ColumnAddress::MemorySubtree(idx) => {
                self.push(&format!(
                    "GET_MEMORY_PLACE({type_tag}, {new_ident}, {idx})\n"
                ));
            }
            ColumnAddress::SetupSubtree(_idx) => {
                todo!();
            }
            ColumnAddress::OptimizedOut(idx) => {
                assert!(self.scratch_size > idx);
                self.push(&format!(
                    "GET_SCRATCH_PLACE({type_tag}, {new_ident}, {idx})\n"
                ));
            }
        }
        new_ident
    }

    /// Emit `CONSTANT(type_tag, new_ident, literal)\n`.
    fn emit_constant(&mut self, type_tag: &str, literal: impl std::fmt::Display) -> usize {
        let new_ident = self.create_var();
        self.push(&format!("CONSTANT({type_tag}, {new_ident}, {literal})\n"));
        new_ident
    }

    /// Emit `GET_ORACLE_VALUE(type_tag, new_ident, placeholder_ident)\n`.
    fn emit_oracle_value(&mut self, type_tag: &str, placeholder: &Placeholder) -> usize {
        let new_ident = self.create_var();
        let placeholder_ident = Self::get_placeholder_ident(placeholder);
        self.push(&format!(
            "GET_ORACLE_VALUE({type_tag}, {new_ident}, {placeholder_ident})\n"
        ));
        new_ident
    }

    fn add_expression(&mut self, expr: &RawExpression<F>) {
        match expr {
            RawExpression::Bool(expr) => {
                self.add_boolean_expr(expr);
            }
            RawExpression::Field(expr) => {
                self.add_field_expr(expr);
            }
            RawExpression::Integer(expr) => {
                self.add_integer_expr(expr);
            }
            RawExpression::PerformLookup {
                input_subexpr_idxes, // subexpressions
                table_id_subexpr_idx,
                num_outputs,
                lookup_mapping_idx,
            } => {
                let lookup_mapping_idx = *lookup_mapping_idx;
                assert!(
                    lookup_mapping_idx < self.num_lookup_mappings,
                    "expression refers to lookup number {}, while only {} exist in scope",
                    lookup_mapping_idx,
                    self.num_lookup_mappings
                );
                let new_ident = self.create_var();
                let num_inputs = input_subexpr_idxes.len();
                let num_outputs = *num_outputs;
                let table_id = *table_id_subexpr_idx;
                if num_outputs > 0 {
                    self.push(&format!("LOOKUP({new_ident}, {num_inputs}, {num_outputs}, {table_id}, {lookup_mapping_idx}"));
                } else {
                    self.push(&format!(
                        "LOOKUP_ENFORCE({num_inputs}, {table_id}, {lookup_mapping_idx}"
                    ));
                }
                for input in input_subexpr_idxes {
                    self.push(&format!(", VAR({input})"));
                }
                self.push(")\n");
            }
            RawExpression::MaybePerformLookup {
                input_subexpr_idxes, // subexpressions
                table_id_subexpr_idx,
                mask_id_subexpr_idx,
                num_outputs,
            } => {
                let new_ident = self.create_var();
                let num_inputs = input_subexpr_idxes.len();
                let num_outputs = *num_outputs;
                let table_id = *table_id_subexpr_idx;
                let mask_id = *mask_id_subexpr_idx;
                self.push(&format!(
                    "MAYBE_LOOKUP({new_ident}, {num_inputs}, {num_outputs}, {table_id}, {mask_id}"
                ));
                for input in input_subexpr_idxes {
                    self.push(&format!(", VAR({input})"));
                }
                self.push(")\n");
            }
            RawExpression::AccessLookup {
                subindex,
                output_index,
            } => {
                let var_ident = *subindex;
                let new_ident = self.create_var();
                self.push(&format!(
                    "ACCESS_LOOKUP({new_ident}, {var_ident}, {output_index})\n"
                ));
            }
            RawExpression::WriteVariable {
                into_variable,
                source_subexpr, // it'll be only subexpression, but we need type
                condition_subexpr_idx,
            } => {
                // this is an expression in SSA, so we should update index
                self.next_var_idx += 1;
                let address = self.get_column_address(into_variable);
                match address {
                    ColumnAddress::WitnessSubtree(idx) => {
                        let source_ident = self.expression_into_var(source_subexpr);
                        if let Some(condition) = condition_subexpr_idx {
                            let condition_ident = *condition;
                            // For a column that is ONLY ever written under a guard, fold the
                            // zero-default into its FIRST write (in evaluation order): emit a
                            // branchless `cond ? source : 0` store instead of an `IF`, so rows
                            // whose guard is false get a definite zero with no separate prologue.
                            // Later writes (mutually-exclusive opcode branches) stay `IF` and
                            // overwrite where they fire.
                            if self.conditional_only_witness.contains(&idx)
                                && self.witness_zero_default_emitted.insert(idx)
                            {
                                self.push(&format!(
                                    "SET_WITNESS_PLACE_OR_ZERO({idx}, {condition_ident}, {source_ident})\n"
                                ));
                            } else {
                                self.push(&format!(
                                    "IF({condition_ident}, SET_WITNESS_PLACE({idx}, {source_ident}))\n"
                                ));
                            }
                        } else {
                            self.output
                                .push_str(&format!("SET_WITNESS_PLACE({idx}, {source_ident})\n"));
                        }
                    }
                    ColumnAddress::MemorySubtree(_idx) => {
                        if self.write_into_memory {
                            unimplemented!("--write-memory: memory-subtree writes not implemented")
                        } else {
                            // do nothing and rely on the generic procedure. Hope that compiler optimizes out unused expressions
                        }
                    }
                    ColumnAddress::SetupSubtree(_idx) => {
                        unreachable!("can not write to setup");
                    }
                    ColumnAddress::OptimizedOut(idx) => {
                        let source_ident = self.expression_into_var(source_subexpr);
                        self.scratch_size = std::cmp::max(self.scratch_size, idx + 1);
                        if let Some(condition) = condition_subexpr_idx {
                            let condition_ident = *condition;
                            self.push(&format!(
                                "IF({condition_ident}, SET_SCRATCH_PLACE({idx}, {source_ident}))\n"
                            ));
                        } else {
                            self.output
                                .push_str(&format!("SET_SCRATCH_PLACE({idx}, {source_ident})\n"));
                        }
                    }
                };
            }
        }
    }

    fn generate_header(&mut self, table_offsets: &[u32]) {
        self.push("LOOKUP_TABLE_OFFSETS(");
        for (i, offset) in table_offsets.iter().enumerate() {
            if i != 0 {
                self.push(", ");
            }
            self.push(&format!("{offset}"));
        }
        self.push(")\n");
        self.push("\n");
    }

    fn generate_functions(
        &mut self,
        graph: &[Vec<RawExpression<F>>],
        layout: &BTreeMap<Variable, ColumnAddress>,
    ) {
        for (index, expressions) in graph.iter().enumerate() {
            self.next_var_idx = 0;
            self.generate_function(layout, index, expressions);
        }
    }

    fn generate_function(
        &mut self,
        layout: &BTreeMap<Variable, ColumnAddress>,
        index: usize,
        expressions: &[RawExpression<F>],
    ) {
        // quickly check that if all outputs are into memory, then we can skip such cases
        if !self.write_into_memory {
            let mut can_skip = true;
            for expr in expressions.iter() {
                if let RawExpression::WriteVariable { into_variable, .. } = expr {
                    let place = layout[into_variable];
                    match place {
                        ColumnAddress::MemorySubtree(..) => {}
                        _ => {
                            can_skip = false;
                            break;
                        }
                    }
                }
                if let RawExpression::PerformLookup { .. } = expr {
                    // we can not skip it as we will need to count multiplicity
                    can_skip = false;
                    break;
                }
            }
            if can_skip {
                return;
            }
        }
        self.push("FN_BEGIN(");
        self.push(&index.to_string());
        self.push(")\n");
        for expression in expressions {
            self.add_expression(expression);
        }
        self.push("FN_END\n\n");
        self.fn_indexes.push(index);
    }

    fn generate_footer(&mut self) {
        let scratch_size = self.scratch_size;
        self.push("FN_BEGIN(generate)\n");
        for index in self.fn_indexes.clone().into_iter() {
            self.push("FN_CALL(");
            self.push(&index.to_string());
            self.push(")\n");
        }
        self.push("FN_END\n");
        self.push("\n");
        let scratch = if scratch_size == 0 {
            "constexpr wrapped_f *scratch = nullptr;\n".to_string()
        } else {
            "wrapped_f *scratch = scratch_storage + gid;\n".to_string()
        };
        self.push(&format!("#define SCRATCH {scratch}\n"));
    }

    pub fn generate(
        graph: &[Vec<RawExpression<F>>],
        circuit: &GKRCircuitArtifact<F>,
        perform_assignments_to_memory: bool,
    ) -> String {
        let num_lookup_mappings = circuit.num_generic_lookups;
        let mut layout = BTreeMap::new();
        let mut next_scratch_slot = 0usize;
        for (var, pos) in circuit.placement_data.iter() {
            match pos {
                GKRAddress::BaseLayerMemory(offset) => {
                    layout.insert(*var, ColumnAddress::MemorySubtree(*offset));
                }
                GKRAddress::BaseLayerWitness(offset) => {
                    layout.insert(*var, ColumnAddress::WitnessSubtree(*offset));
                }
                GKRAddress::InnerLayer { .. }
                | GKRAddress::Cached { .. }
                | GKRAddress::ScratchSpace(..) => {
                    layout.insert(*var, ColumnAddress::OptimizedOut(next_scratch_slot));
                    next_scratch_slot += 1;
                }
                GKRAddress::VirtualSetup(virtual_setup) => {
                    let setup_index = match virtual_setup {
                        VirtualSetupPoly::RangeCheck16Bits => 0,
                        VirtualSetupPoly::RangeCheckTimestamp => 1,
                        VirtualSetupPoly::InitsAndTeardownsLow => 2,
                        VirtualSetupPoly::InitsAndTeardownsHigh => 3,
                    };
                    layout.insert(*var, ColumnAddress::SetupSubtree(setup_index));
                }
                GKRAddress::Setup(..) => {
                    unreachable!("setup placements are not expected in GPU witness generation")
                }
            }
        }
        let mut generator =
            Generator::new(&layout, num_lookup_mappings, perform_assignments_to_memory);
        generator.generate_header(&circuit.table_offsets);
        generator.collect_conditional_only_witness(graph);
        generator.generate_functions(graph, &layout);
        generator.generate_footer();
        generator.output
    }
}

pub fn generate_from_files(
    layout_path: impl AsRef<Path>,
    ssa_path: impl AsRef<Path>,
    perform_assignments_to_memory: bool,
) -> Result<String, Box<dyn std::error::Error>> {
    let layout = File::open(layout_path)?;
    let ssa = File::open(ssa_path)?;
    let compiled_circuit: GKRCircuitArtifact<F> = serde_json::from_reader(layout)?;
    let compiled_graph: Vec<Vec<RawExpression<F>>> = serde_json::from_reader(ssa)?;

    Ok(Generator::generate(
        &compiled_graph,
        &compiled_circuit,
        perform_assignments_to_memory,
    ))
}

/// A circuit whose witness-generation CUDA body is generated from committed
/// SSA/layout inputs and checked in under `circuit_defs/`.
///
/// The generator is a pure function of `(layout, ssa)`, so each committed
/// artifact must stay byte-identical to a fresh regeneration. The
/// `committed_witness_cuh_is_current` test enforces that; the
/// `regenerate_committed` binary refreshes the artifacts after an intentional
/// codegen change.
pub struct GeneratedCircuit {
    /// Base name of the `cs/compiled_circuits/{id}_{layout,ssa}_gkr.json` inputs.
    pub id: &'static str,
    /// Repo-relative path of the checked-in `witness_generation_fn.cuh`.
    pub committed_cuh: &'static str,
}

impl GeneratedCircuit {
    /// Regenerate this circuit's witness-generation CUDA from its committed
    /// inputs, exactly as the checked-in artifact was produced
    /// (`perform_assignments_to_memory = false`).
    pub fn regenerate(&self, repo_root: &Path) -> Result<String, Box<dyn std::error::Error>> {
        let layout = repo_root.join(format!("cs/compiled_circuits/{}_layout_gkr.json", self.id));
        let ssa = repo_root.join(format!("cs/compiled_circuits/{}_ssa_gkr.json", self.id));
        generate_from_files(layout, ssa, false)
    }

    /// Absolute path of the checked-in artifact under `repo_root`.
    pub fn committed_path(&self, repo_root: &Path) -> PathBuf {
        repo_root.join(self.committed_cuh)
    }
}

/// Every circuit with a committed `witness_generation_fn.cuh` artifact, paired
/// with its generator input id. Single source of truth shared by the
/// `regenerate_committed` binary and the drift-guard test, so the two halves
/// cannot fall out of sync. Note the id and the committed directory name differ
/// for several circuits (e.g. `blake2_with_extended_control` →
/// `blake2_with_compression`), which is exactly why this mapping is explicit.
pub const CIRCUITS: &[GeneratedCircuit] = &[
    GeneratedCircuit {
        id: "add_sub_lui_auipc_mop",
        committed_cuh: "circuit_defs/unrolled_circuits/add_sub_lui_auipc_mop/generated/witness_generation_fn.cuh",
    },
    GeneratedCircuit {
        id: "bigint_with_extended_control",
        committed_cuh: "circuit_defs/bigint_with_control/generated/witness_generation_fn.cuh",
    },
    GeneratedCircuit {
        id: "blake2_g_function",
        committed_cuh: "circuit_defs/blake2_g_function/generated/witness_generation_fn.cuh",
    },
    GeneratedCircuit {
        id: "blake2_with_extended_control",
        committed_cuh: "circuit_defs/blake2_with_compression/generated/witness_generation_fn.cuh",
    },
    GeneratedCircuit {
        id: "jump_branch_slt",
        committed_cuh: "circuit_defs/unrolled_circuits/jump_branch_slt/generated/witness_generation_fn.cuh",
    },
    GeneratedCircuit {
        id: "keccak_special5",
        committed_cuh: "circuit_defs/keccak_special5/generated/witness_generation_fn.cuh",
    },
    GeneratedCircuit {
        id: "mem_subword_only",
        committed_cuh: "circuit_defs/unrolled_circuits/load_store_subword_only/generated/witness_generation_fn.cuh",
    },
    GeneratedCircuit {
        id: "mem_word_only",
        committed_cuh: "circuit_defs/unrolled_circuits/load_store_word_only/generated/witness_generation_fn.cuh",
    },
    GeneratedCircuit {
        id: "shift_binop",
        committed_cuh: "circuit_defs/unrolled_circuits/shift_binary/generated/witness_generation_fn.cuh",
    },
    GeneratedCircuit {
        id: "unified_reduced_machine",
        committed_cuh: "circuit_defs/unrolled_circuits/unified_reduced_machine/generated/witness_generation_fn.cuh",
    },
    GeneratedCircuit {
        id: "unsigned_mul_div",
        committed_cuh: "circuit_defs/unrolled_circuits/mul_div_unsigned/generated/witness_generation_fn.cuh",
    },
];

/// Absolute path to the repository root. This crate lives at
/// `<root>/gpu/witness_eval_generator`, so the root is two levels up from
/// `CARGO_MANIFEST_DIR` (stable regardless of the process working directory).
pub fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("resolve repository root from CARGO_MANIFEST_DIR")
}

#[cfg(test)]
mod tests {
    use crate::{CIRCUITS, repo_root};
    use std::collections::HashSet;
    use std::path::Path;

    /// A readable description of the first byte where `generated` and
    /// `committed` differ. Byte-level (matching the pass/fail comparison), so it
    /// never misattributes a whitespace/line-ending/trailing difference — it
    /// reports the exact offset, the containing line, and both sides' text.
    fn first_diff(generated: &str, committed: &str) -> String {
        let (gb, cb) = (generated.as_bytes(), committed.as_bytes());
        match gb.iter().zip(cb).position(|(a, b)| a != b) {
            Some(offset) => {
                let line = gb[..offset].iter().filter(|&&b| b == b'\n').count() + 1;
                let g = generated.lines().nth(line - 1).unwrap_or("");
                let c = committed.lines().nth(line - 1).unwrap_or("");
                format!(
                    "first differs at byte {offset} (line {line}): generated {g:?} vs committed {c:?}"
                )
            }
            None => format!(
                "one is a prefix of the other: generated {} bytes vs committed {} bytes",
                gb.len(),
                cb.len()
            ),
        }
    }

    /// Every committed `witness_generation_fn.cuh` under `circuit_defs/`,
    /// repo-relative with `/` separators (matching `CIRCUITS.committed_cuh`).
    fn collect_committed_cuh(dir: &Path, root: &Path, out: &mut Vec<String>) {
        for entry in std::fs::read_dir(dir).expect("read circuit_defs") {
            let path = entry.expect("dir entry").path();
            if path.is_dir() {
                collect_committed_cuh(&path, root, out);
            } else if path.file_name().and_then(|n| n.to_str()) == Some("witness_generation_fn.cuh")
            {
                let rel = path.strip_prefix(root).expect("under repo root");
                out.push(rel.to_str().expect("utf-8 path").to_owned());
            }
        }
    }

    /// Drift guard: every committed `witness_generation_fn.cuh` must match a
    /// fresh regeneration from its committed SSA/layout inputs. Runs in CI (no
    /// `skip_if_ci`) — the generator is pure and its inputs are checked in, so
    /// this is a cheap, deterministic, GPU-free check.
    #[test]
    fn committed_witness_cuh_is_current() {
        let root = repo_root();
        let mut stale = Vec::new();
        for circuit in CIRCUITS {
            let generated = circuit
                .regenerate(&root)
                .unwrap_or_else(|e| panic!("generator failed for {}: {e}", circuit.id));
            let committed_path = circuit.committed_path(&root);
            let committed = std::fs::read_to_string(&committed_path).unwrap_or_else(|e| {
                panic!(
                    "cannot read committed artifact {}: {e}",
                    committed_path.display()
                )
            });
            if generated != committed {
                stale.push(format!(
                    "  {} -> {}\n      {}",
                    circuit.id,
                    circuit.committed_cuh,
                    first_diff(&generated, &committed)
                ));
            }
        }
        assert!(
            stale.is_empty(),
            "Committed witness-generation CUDA is stale vs current codegen:\n{}\n\n\
             Regenerate and commit with:\n    \
             cargo run -p gpu_witness_eval_generator --bin regenerate_committed",
            stale.join("\n")
        );
    }

    /// Completeness guard: every committed `witness_generation_fn.cuh` under
    /// `circuit_defs/` must be listed in `CIRCUITS`. Without this, a future
    /// artifact added without a table entry would be silently unguarded by
    /// `committed_witness_cuh_is_current`.
    #[test]
    fn every_committed_cuh_is_listed() {
        let root = repo_root();
        let listed: HashSet<&str> = CIRCUITS.iter().map(|c| c.committed_cuh).collect();
        let mut found = Vec::new();
        collect_committed_cuh(&root.join("circuit_defs"), &root, &mut found);
        let missing: Vec<&String> = found
            .iter()
            .filter(|p| !listed.contains(p.as_str()))
            .collect();
        assert!(
            missing.is_empty(),
            "committed witness CUDA not covered by CIRCUITS (add each to the table):\n{}",
            missing
                .iter()
                .map(|p| format!("  {p}"))
                .collect::<Vec<_>>()
                .join("\n")
        );
        // Guard against a mis-resolved root vacuously passing: we must have
        // found exactly as many artifacts as the table lists.
        assert_eq!(
            found.len(),
            CIRCUITS.len(),
            "found {} committed .cuh under circuit_defs but CIRCUITS lists {}",
            found.len(),
            CIRCUITS.len()
        );
    }
}
