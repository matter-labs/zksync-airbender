#![expect(warnings)]
#![allow(incomplete_features)]
#![feature(generic_const_exprs)]
#![feature(array_chunks)]
#![feature(iter_array_chunks)]
#![feature(let_chains)]

pub mod abstractions;
pub mod cycle;
pub mod mmio;
pub mod mmu;
mod qol;
pub mod runner;
pub mod sim;
pub mod utils;

#[cfg(feature = "delegation")]
pub mod delegations;

#[cfg(test)]
mod tests;

pub mod setup {
    use std::marker::PhantomData;

    use crate::{
        abstractions::{
            memory::{MemorySource, VectorMemoryImpl},
            non_determinism::{NonDeterminismCSRSource, QuasiUARTSource}
        },
        cycle::{
            state::RiscV32MachineV1,
            IMStandardIsaConfig,
            MachineConfig
        },
        mmu::NoMMU,
        sim::{RiscV32Machine, RiscV32MachineSetup}
    };

    #[derive(Default)]
    pub struct DefaultSetup();

    impl RiscV32MachineSetup for DefaultSetup {
        type ND = QuasiUARTSource;
        type MS = VectorMemoryImpl;
        type TR = ();
        type MMU = NoMMU;
        type C = IMStandardIsaConfig;

        type M = RiscV32MachineV1<Self::MS, (), NoMMU, Self::ND, Self::C>;

    }

    pub struct BaselineWithND<ND, C> 
    where 
        ND: NonDeterminismCSRSource<VectorMemoryImpl>,
        C: MachineConfig,
    {
        non_determinism_source: ND,
        phantom: PhantomData<(C)>,
    }

    impl<ND, C> BaselineWithND<ND, C> 
    where
        ND: NonDeterminismCSRSource<VectorMemoryImpl>,
        C: MachineConfig,
    {
        pub fn new(non_determinism_source: ND) -> Self {
            Self {
                non_determinism_source, phantom: PhantomData
            }
        }
    }

    impl<ND, C> RiscV32MachineSetup for BaselineWithND<ND, C> 
    where
        ND: NonDeterminismCSRSource<VectorMemoryImpl>,
        C: MachineConfig,
    {
        type ND = ND;
        type MS = VectorMemoryImpl;
        type TR = ();
        type MMU = NoMMU;
        type C = C;

        type M = RiscV32MachineV1<Self::MS, (), NoMMU, Self::ND, Self::C>;

        fn instantiate(self, config: &crate::sim::SimulatorConfig) -> Self::M {
            let mut machine = RiscV32MachineV1::with_nd(config.entry_point, self.non_determinism_source);
            machine.populate_memory(config.entry_point, config.bin.to_iter());
            machine
        }
    }
}
