use crate::cs::placeholder::Placeholder;
use crate::types::Register;
use crate::{cs::circuit::Circuit, types::Boolean};
use field::PrimeField;

#[derive(Clone, Copy, Debug)]
pub struct PcWrapper<F: PrimeField> {
    pub pc: Register<F>,
}

impl<F: PrimeField> PcWrapper<F> {
    pub fn initialize<C: Circuit<F>>(cs: &mut C) -> Self {
        // NOTE: it should go up in the call chain, but there is a duplicating comment at the start of the
        // state transition description. PC goes through the series of table lookups that ensure that it is 16 bits
        let pc = Register::<F>::new_unchecked_from_placeholder(cs, Placeholder::PcInit);
        Self { pc }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct AuxDataConditional {
    exec_flag: Boolean,
    condition: Boolean,
}

impl AuxDataConditional {
    pub const fn uninitialized() -> Self {
        AuxDataConditional {
            exec_flag: Boolean::uninitialized(),
            condition: Boolean::uninitialized(),
        }
    }

    pub fn new(exec_flag: Boolean, condition: Boolean) -> Self {
        AuxDataConditional {
            exec_flag,
            condition,
        }
    }

    #[track_caller]
    pub fn choose_from_orthogonal_variants<F: PrimeField, C: Circuit<F>>(
        cs: &mut C,
        variants: &[Self],
    ) -> Boolean {
        let (exec_flags, conditions): (Vec<_>, Vec<_>) =
            variants.iter().map(|e| (e.exec_flag, e.condition)).unzip();
        let flag = Boolean::choose_from_orthogonal_flags::<F, C>(cs, &exec_flags, &conditions);

        flag
    }
}

#[derive(Clone, Copy, Debug)]
pub struct AuxDataArr<F: PrimeField> {
    exec_flag: Boolean,
    trapped: Boolean,
    mem_dst_value: Register<F>,
    rd: Register<F>,
}

impl<F: PrimeField> AuxDataArr<F> {
    pub fn new(
        exec_flag: Boolean,
        trapped: Boolean,
        mem_dst_value: Register<F>,
        rd: Register<F>,
    ) -> Self {
        AuxDataArr {
            exec_flag,
            trapped,
            mem_dst_value,
            rd,
        }
    }

    pub const fn uninitialized() -> Self {
        AuxDataArr {
            exec_flag: Boolean::uninitialized(),
            trapped: Boolean::uninitialized(),
            mem_dst_value: Register::<F>::uninitialized(),
            rd: Register::<F>::uninitialized(),
        }
    }

    #[track_caller]
    pub fn choose_from_orthogonal_variants<C: Circuit<F>>(
        cs: &mut C,
        variants: &[Self],
    ) -> (Boolean, Register<F>, Register<F>) {
        let (flags, trapped_ops, mem_dst_ops, rd_ops): (Vec<_>, Vec<_>, Vec<_>, Vec<_>) = {
            itertools::multiunzip(
                variants
                    .iter()
                    .map(|elem| (elem.exec_flag, elem.trapped, elem.mem_dst_value, elem.rd)),
            )
        };
        let trapped = Boolean::choose_from_orthogonal_flags::<F, C>(cs, &flags, &trapped_ops);
        let mem_dst = Register::choose_from_orthogonal_variants::<C>(cs, &flags, &mem_dst_ops);
        let rd = Register::choose_from_orthogonal_variants::<C>(cs, &flags, &rd_ops);

        (trapped, mem_dst, rd)
    }
}
