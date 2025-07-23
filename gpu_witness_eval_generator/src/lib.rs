use ::field::Mersenne31Field;
use cs::cs::placeholder::Placeholder;
use cs::cs::witness_placer::graph_description::{
    BoolNodeExpression, Expression, FieldNodeExpression, FixedWidthIntegerNodeExpression,
    RawExpression,
};
use cs::definitions::{ColumnAddress, Variable};
use cs::one_row_compiler::CompiledCircuitArtifact;
use std::collections::BTreeMap;

mod boolean;
mod field;
mod integer;

type F = Mersenne31Field;

pub struct Generator {
    write_into_memory: bool,
    layout: BTreeMap<Variable, ColumnAddress>,
    num_lookup_mappings: usize,
    next_var_idx: usize,
    output: String,
    scratch_size: usize,
    fn_indexes: Vec<usize>,
}

impl Generator {
    fn new(
        layout: &BTreeMap<Variable, ColumnAddress>,
        num_lookup_mappings: usize,
        write_into_memory: bool,
    ) -> Self {
        Self {
            layout: layout.clone(),
            num_lookup_mappings,
            write_into_memory,
            next_var_idx: 0,
            output: String::new(),
            scratch_size: 0,
            fn_indexes: Vec::new(),
        }
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

    fn ident_for_idx(idx: usize) -> usize {
        idx
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
            a @ _ => {
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
                let table_id = Self::ident_for_idx(*table_id_subexpr_idx);
                if num_outputs > 0 {
                    self.push(&format!("LOOKUP({new_ident}, {num_inputs}, {num_outputs}, {table_id}, {lookup_mapping_idx}"));
                } else {
                    self.push(&format!(
                        "LOOKUP_ENFORCE({num_inputs}, {table_id}, {lookup_mapping_idx}"
                    ));
                }
                for input in input_subexpr_idxes.iter().copied().map(Self::ident_for_idx) {
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
                let table_id = Self::ident_for_idx(*table_id_subexpr_idx);
                let mask_id = Self::ident_for_idx(*mask_id_subexpr_idx);
                self.push(&format!(
                    "MAYBE_LOOKUP({new_ident}, {num_inputs}, {num_outputs}, {table_id}, {mask_id}"
                ));
                for input in input_subexpr_idxes.iter().copied().map(Self::ident_for_idx) {
                    self.push(&format!(", VAR({input})"));
                }
                self.push(")\n");
            }
            RawExpression::AccessLookup {
                subindex,
                output_index,
            } => {
                let var_ident = Self::ident_for_idx(*subindex);
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
                            let condition_ident = Self::ident_for_idx(*condition);
                            self.push(&format!(
                                "IF({condition_ident}, SET_WITNESS_PLACE({idx}, {source_ident}))\n"
                            ));
                        } else {
                            self.output
                                .push_str(&format!("SET_WITNESS_PLACE({idx}, {source_ident})\n"));
                        }
                    }
                    ColumnAddress::MemorySubtree(_idx) => {
                        if self.write_into_memory {
                            todo!()
                        } else {
                            // do nothing and rely on the generic procedure. Hope that compiler optimizes out unused expressions
                            // quote! {}
                        }
                    }
                    ColumnAddress::SetupSubtree(_idx) => {
                        unreachable!("can not write to setup");
                    }
                    ColumnAddress::OptimizedOut(idx) => {
                        let source_ident = self.expression_into_var(source_subexpr);
                        self.scratch_size = std::cmp::max(self.scratch_size, idx + 1);
                        if let Some(condition) = condition_subexpr_idx {
                            let condition_ident = Self::ident_for_idx(*condition);
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
        if self.write_into_memory == false {
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
            format!("wrapped_f scratch[{scratch_size}];\n")
        };
        self.push(&format!("#define SCRATCH {scratch}\n"));
    }

    pub fn generate(
        graph: &[Vec<RawExpression<F>>],
        circuit: &CompiledCircuitArtifact<F>,
        perform_assignments_to_memory: bool,
    ) -> String {
        let num_lookup_mappings = circuit.witness_layout.width_3_lookups.len();
        let layout = &circuit.variable_mapping;
        let mut generator =
            Generator::new(layout, num_lookup_mappings, perform_assignments_to_memory);
        generator.generate_header(&circuit.table_offsets);
        generator.generate_functions(graph, layout);
        generator.generate_footer();
        generator.output
    }
}

#[cfg(test)]
mod tests {
    use crate::F;
    use cs::cs::witness_placer::graph_description::RawExpression;
    use cs::one_row_compiler::CompiledCircuitArtifact;
    use serde::de;
    use std::fs::File;
    use std::io::Write;

    fn deserialize_from_file<T: de::DeserializeOwned>(filename: &str) -> T {
        let src = File::open(filename).unwrap();
        serde_json::from_reader(src).unwrap()
    }

    fn generate(id: &str) {
        let layout_path = format!("../cs/{id}_layout.json");
        let ssa_path = format!("../cs/{id}_ssa.json");
        let generated_cu_path = format!("{id}.cuh");
        // println!("{layout_path}");
        let compiled_circuit: CompiledCircuitArtifact<F> = deserialize_from_file(&layout_path);
        // println!("{ssa_path}");
        let compiled_graph: Vec<Vec<RawExpression<F>>> = deserialize_from_file(&ssa_path);
        println!("{generated_cu_path}");
        let code = super::Generator::generate(&compiled_graph, &compiled_circuit, false);
        File::create(&generated_cu_path)
            .unwrap()
            .write_all(&code.as_bytes())
            .unwrap();
    }

    #[test]
    fn launch() {
        generate("bigint_delegation");
        generate("blake_delegation");
        generate("full_machine_with_delegation");
        generate("keccak_delegation");
        generate("minimal_machine_with_delegation");
    }
}
