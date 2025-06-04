use super::ops::*;
use super::*;
// use crate::machine::machine_configurations::minimal_no_exceptions::basic_state_transition::reduced_isa_state_transition;
use crate::machine::machine_configurations::minimal_no_exceptions::optimized_state_transition::optimized_reduced_isa_state_transition;
use minimal_state::MinimalStateRegistersInMemory;

type ST<F> = MinimalStateRegistersInMemory<F>;
type BS = BasicFlagsSource;

// type RS<F> = RegisterDecomposition<F>;
// type DE<F> = BasicDecodingResultWithoutSigns<F>;

type RS<F> = RegisterDecompositionWithSign<F>;
type DE<F> = BasicDecodingResultWithSigns<F>;

#[derive(Clone, Copy, Debug, Default)]
pub struct MinimalMachineNoExceptionHandlingWithDelegation;

impl<F: PrimeField> Machine<F> for MinimalMachineNoExceptionHandlingWithDelegation {
    const ASSUME_TRUSTED_CODE: bool = true;
    const OUTPUT_EXACT_EXCEPTIONS: bool = false;
    const USE_ROM_FOR_BYTECODE: bool = true;

    type State = MinimalStateRegistersInMemory<F>;

    fn all_supported_opcodes() -> Vec<Box<dyn DecodableMachineOp>> {
        vec![
            Box::new(AddOp),
            Box::new(SubOp),
            Box::new(LuiOp),
            Box::new(AuiPc),
            Box::new(BinaryOp),
            Box::new(ConditionalOp::<true>),
            Box::new(ShiftOp::<true, false>),
            Box::new(JumpOp),
            Box::new(LoadOp::<false, false>),
            Box::new(StoreOp::<false>),
            Box::new(MopOp),
            Box::new(CsrOp::<false, false, false>),
        ]
    }

    fn define_used_tables() -> BTreeSet<TableType> {
        let mut set = BTreeSet::new();
        set.extend(<AddOp as MachineOp<F, ST<F>, RS<F>, DE<F>, BS>>::define_used_tables());
        set.extend(<SubOp as MachineOp<F, ST<F>, RS<F>, DE<F>, BS>>::define_used_tables());
        set.extend(<LuiOp as MachineOp<F, ST<F>, RS<F>, DE<F>, BS>>::define_used_tables());
        set.extend(<AuiPc as MachineOp<F, ST<F>, RS<F>, DE<F>, BS>>::define_used_tables());
        set.extend(<BinaryOp as MachineOp<F, ST<F>, RS<F>, DE<F>, BS>>::define_used_tables());
        set.extend(<ConditionalOp<true> as MachineOp<
            F,
            ST<F>,
            RS<F>,
            DE<F>,
            BS,
        >>::define_used_tables());
        set.extend(<ShiftOp<true, true> as MachineOp<
            F,
            ST<F>,
            RS<F>,
            DE<F>,
            BS,
        >>::define_used_tables());
        set.extend(<JumpOp as MachineOp<F, ST<F>, RS<F>, DE<F>, BS>>::define_used_tables());
        set.extend(<LoadOp<false, false> as MachineOp<
            F,
            ST<F>,
            RS<F>,
            DE<F>,
            BS,
        >>::define_used_tables());
        set.extend(<StoreOp<false> as MachineOp<F, ST<F>, RS<F>, DE<F>, BS>>::define_used_tables());
        set.extend(<MopOp as MachineOp<F, ST<F>, RS<F>, DE<F>, BS>>::define_used_tables());
        // set.extend(<CsrOp::<false, false> as MachineOp::<F, ST<F>, RS<F>, DE<F>, BS>>::define_used_tables());

        set
    }

    fn describe_state_transition<CS: Circuit<F>, const ROM_ADDRESS_SPACE_SECOND_WORD_BITS: usize>(
        cs: &mut CS,
    ) -> (Self::State, Self::State)
    where
        [(); { <Self as Machine<F>>::ASSUME_TRUSTED_CODE } as usize]:,
        [(); { <Self as Machine<F>>::OUTPUT_EXACT_EXCEPTIONS } as usize]:,
    {
        let (splitting, _) = <Self as Machine<F>>::produce_decoder_table_stub();
        let boolean_keys = <Self as Machine<F>>::all_decoder_keys();

        optimized_reduced_isa_state_transition::<
            F,
            CS,
            { <Self as Machine<F>>::ASSUME_TRUSTED_CODE },
            { <Self as Machine<F>>::OUTPUT_EXACT_EXCEPTIONS },
            true,
            ROM_ADDRESS_SPACE_SECOND_WORD_BITS,
        >(
            cs,
            // <Self::State as BaseMachineState<F>>::opcodes_are_in_rom(),
            splitting,
            boolean_keys,
        )
    }
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::utils::serialize_to_file;
    use field::Mersenne31Field;

    const SECOND_WORD_BITS: usize = 4;

    #[test]
    fn compile_minimal_machine_with_delegation() {
        let machine = MinimalMachineNoExceptionHandlingWithDelegation;
        let rom_table = create_table_for_rom_image::<_, SECOND_WORD_BITS>(
            &[],
            TableType::RomRead.to_table_id(),
        );
        let csr_table = create_csr_table_for_delegation(
            true,
            &[1991],
            TableType::SpecialCSRProperties.to_table_id(),
        );

        let compiled =
            default_compile_machine::<_, SECOND_WORD_BITS>(machine, rom_table, Some(csr_table), 20);
        serialize_to_file(&compiled, "minimal_machine_with_delegation_layout.json");
    }

    #[test]
    fn reduced_machine_with_delegation_get_witness_graph() {
        let machine = MinimalMachineNoExceptionHandlingWithDelegation;
        let ssa_forms = dump_ssa_witness_eval_form::<Mersenne31Field, _, SECOND_WORD_BITS>(machine);
        serialize_to_file(&ssa_forms, "minimal_machine_with_delegation_ssa.json");
    }
}
