use super::ops::*;
use super::*;
use minimal_state::MinimalStateRegistersInMemory;

// pub(crate) mod basic_state_transition;
// use self::basic_state_transition::*;

pub(crate) mod optimized_state_transition;
use self::optimized_state_transition::*;

type ST<F> = MinimalStateRegistersInMemory<F>;
type BS = BasicFlagsSource;

type RS<F> = RegisterDecompositionWithSign<F>;
type DE<F> = BasicDecodingResultWithSigns<F>;

#[derive(Clone, Copy, Debug, Default)]
pub struct MinimalMachineNoExceptionHandling;

impl<F: PrimeField> Machine<F> for MinimalMachineNoExceptionHandling {
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
            // Box::new(MulOp::<false>),
            // Box::new(DivRemOp::<false>),
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
        // set.extend(<MulOp<false> as MachineOp<F, ST<F>, RS<F>, DE<F>, BS>>::define_used_tables());
        // set.extend(
        //     <DivRemOp<false> as MachineOp<F, ST<F>, RS<F>, DE<F>, BS>>::define_used_tables(),
        // );
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
            false,
            ROM_ADDRESS_SPACE_SECOND_WORD_BITS,
        >(
            cs,
            // <Self::State as BaseMachineState<F>>::opcodes_are_in_rom(),
            splitting,
            boolean_keys,
        )
    }
}
