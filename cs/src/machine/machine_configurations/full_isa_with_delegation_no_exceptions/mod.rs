use super::ops::*;
use super::*;
// use crate::machine::machine_configurations::full_isa_no_exceptions::basic_state_transition::base_isa_state_transition;
use crate::machine::machine_configurations::full_isa_no_exceptions::optimized_state_transition::optimized_base_isa_state_transition;
use crate::machine::machine_configurations::minimal_state::MinimalStateRegistersInMemory;

type ST<F> = MinimalStateRegistersInMemory<F>;
type BS = BasicFlagsSource;

type RS<F> = RegisterDecompositionWithSign<F>;
type DE<F> = BasicDecodingResultWithSigns<F>;

#[derive(Clone, Copy, Debug, Default)]
pub struct FullIsaMachineWithDelegationNoExceptionHandling;

impl<F: PrimeField> Machine<F> for FullIsaMachineWithDelegationNoExceptionHandling {
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
            Box::new(MulOp::<true>),
            Box::new(DivRemOp::<true>),
            Box::new(ConditionalOp::<true>),
            Box::new(ShiftOp::<true, false>),
            Box::new(JumpOp),
            Box::new(LoadOp::<true, true>),
            Box::new(StoreOp::<true>),
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
        set.extend(<MulOp<true> as MachineOp<F, ST<F>, RS<F>, DE<F>, BS>>::define_used_tables());
        set.extend(<DivRemOp<true> as MachineOp<F, ST<F>, RS<F>, DE<F>, BS>>::define_used_tables());
        set.extend(<ConditionalOp<true> as MachineOp<
            F,
            ST<F>,
            RS<F>,
            DE<F>,
            BS,
        >>::define_used_tables());
        set.extend(<ShiftOp<true, false> as MachineOp<
            F,
            ST<F>,
            RS<F>,
            DE<F>,
            BS,
        >>::define_used_tables());
        set.extend(<JumpOp as MachineOp<F, ST<F>, RS<F>, DE<F>, BS>>::define_used_tables());
        set.extend(<LoadOp<true, true> as MachineOp<
            F,
            ST<F>,
            RS<F>,
            DE<F>,
            BS,
        >>::define_used_tables());
        set.extend(<StoreOp<true> as MachineOp<F, ST<F>, RS<F>, DE<F>, BS>>::define_used_tables());

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

        // NOTE: it has hardcoded ISA mods inside, so either more configs need to be propagated,
        // or another form of the function must be used

        optimized_base_isa_state_transition::<
            F,
            CS,
            { <Self as Machine<F>>::ASSUME_TRUSTED_CODE },
            { <Self as Machine<F>>::OUTPUT_EXACT_EXCEPTIONS },
            true,
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
    fn compile_full_machine_with_delegation() {
        let machine = FullIsaMachineWithDelegationNoExceptionHandling;
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
        serialize_to_file(&compiled, "full_machine_with_delegation_layout.json");
    }

    #[test]
    fn full_machine_with_delegation_get_witness_graph() {
        let machine = FullIsaMachineWithDelegationNoExceptionHandling;

        let ssa_forms = dump_ssa_witness_eval_form::<Mersenne31Field, _, SECOND_WORD_BITS>(machine);
        serialize_to_file(&ssa_forms, "full_machine_with_delegation_ssa.json");
    }
}
