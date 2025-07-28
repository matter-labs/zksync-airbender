#![expect(warnings)]
#![allow(incomplete_features)]
#![feature(generic_const_exprs)]
#![feature(iter_array_chunks)]

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
            csr_processor::CustomCSRProcessor,
            memory::{MemorySource, VectorMemoryImpl},
            non_determinism::{NonDeterminismCSRSource, QuasiUARTSource},
            tracer::Tracer,
        },
        cycle::{
            state::RiscV32MachineV1,
            state_new::{DelegationCSRProcessor, Riscv32MachineProverUnrolled},
            IMStandardIsaConfig, MachineConfig,
        },
        mmu::NoMMU,
        sim::{RiscV32Machine, RiscV32MachineSetup},
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

        fn instantiate(self, config: &crate::sim::SimulatorConfig) -> Self::M {
            let mut machine =
                RiscV32MachineV1::with_nd(config.entry_point, QuasiUARTSource::default());

            machine
        }
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
                non_determinism_source,
                phantom: PhantomData,
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
            let mut machine =
                RiscV32MachineV1::with_nd(config.entry_point, self.non_determinism_source);
            machine
                .memory_source
                .load_image(config.entry_point, config.bin.to_iter());
            machine
        }
    }

    pub struct ProverUnrolled<MS, TR, ND, CSR, C>
    where
        MS: MemorySource,
        TR: Tracer<C>,
        ND: NonDeterminismCSRSource<MS>,
        CSR: DelegationCSRProcessor,
        C: MachineConfig,
    {
        memory_source: MS,
        memory_tracer: TR,
        non_determinism_source: ND,
        csr_processor: CSR,
        phantom: PhantomData<(C)>,
    }

    impl<MS, TR, ND, CSR, C> ProverUnrolled<MS, TR, ND, CSR, C>
    where
        MS: MemorySource,
        TR: Tracer<C>,
        ND: NonDeterminismCSRSource<MS>,
        CSR: DelegationCSRProcessor,
        C: MachineConfig,
    {
        pub fn new(
            memory_source: MS,
            memory_tracer: TR,
            non_determinism_source: ND,
            csr_processor: CSR,
        ) -> Self {
            Self {
                memory_source,
                memory_tracer,
                non_determinism_source,
                csr_processor,
                phantom: PhantomData,
            }
        }
    }

    impl<MS, TR, ND, CSR, C> RiscV32MachineSetup for ProverUnrolled<MS, TR, ND, CSR, C>
    where
        C: MachineConfig,
        MS: MemorySource,
        TR: Tracer<C>,
        ND: NonDeterminismCSRSource<MS>,
        CSR: DelegationCSRProcessor,
    {
        type ND = ND;
        type MS = MS;
        type TR = TR;
        type MMU = NoMMU;
        type C = C;

        type M = Riscv32MachineProverUnrolled<Self::MS, Self::TR, Self::ND, CSR, Self::C>;

        fn instantiate(self, config: &crate::sim::SimulatorConfig) -> Self::M {
            Riscv32MachineProverUnrolled::new(
                config,
                self.memory_source,
                self.memory_tracer,
                self.non_determinism_source,
                self.csr_processor,
            )
        }
    }
}
