use std::panic::RefUnwindSafe;

use clap::ValueEnum;
use prover::cs::cs::cs_reference::BasicAssembly;
use prover::cs::cs::oracle::ExecutorFamilyDecoderData;
use prover::field::PrimeField;
use rand::rngs::SmallRng;

mod add_sub_lui_auipc_mop;

#[derive(ValueEnum, Clone, Copy, PartialEq, Eq)]
pub enum Circuits {
    AddSubLuiAuipcMop,
}

impl Circuits {
    pub(crate) fn instantiate<F: PrimeField>(&self) -> Box<dyn FuzzTarget<F>> {
        match self {
            Circuits::AddSubLuiAuipcMop => Box::new(add_sub_lui_auipc_mop::Target),
        }
    }
}

pub(crate) trait FuzzTarget<F: PrimeField>: RefUnwindSafe {
    fn name(&self) -> &'static str;
    fn synthesize(&self, cs: &mut BasicAssembly<F>);

    fn random_decoder_data(&self, rng: &mut SmallRng) -> ExecutorFamilyDecoderData;
}
