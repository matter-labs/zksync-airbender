use prover::cs::cs::cs_reference::BasicAssembly;
use prover::cs::cs::oracle::ExecutorFamilyDecoderData;
use prover::cs::machine::ops::unrolled::add_sub_lui_auipc_mop::add_sub_lui_auipc_mop_circuit_with_preprocessed_bytecode;
use prover::cs::machine::ops::unrolled::add_sub_lui_auipc_mop::add_sub_lui_auipc_mop_table_addition_fn;
use prover::field::PrimeField;
use rand::prelude::SmallRng;
use rand::Rng as _;

use crate::witgen::FuzzTarget;

pub(crate) struct Target;

impl<F: PrimeField> FuzzTarget<F> for Target {
    fn name(&self) -> &'static str {
        "add_sub_lui_auipc_mop"
    }

    fn synthesize(&self, cs: &mut BasicAssembly<F>) {
        add_sub_lui_auipc_mop_table_addition_fn(cs);
        add_sub_lui_auipc_mop_circuit_with_preprocessed_bytecode(cs);
    }

    fn random_decoder_data(&self, rng: &mut SmallRng) -> ExecutorFamilyDecoderData {
        let imm = rng.next_u32();
        let rs1_index = rng.next_u32() as u8;
        let rs2_index = rng.next_u32() as u8;
        let rd_index = rng.next_u32() as u8;
        let rd_is_zero = rd_index == 0;
        let funct3 = rng.next_u32() as u8;
        let funct7 = None;
        // One-hot encoding of 8 elements.
        let opcode_family_bits = 1u32 << (rng.next_u32() % 8);
        ExecutorFamilyDecoderData {
            imm,
            rs1_index,
            rs2_index,
            rd_index,
            rd_is_zero,
            funct3,
            funct7,
            opcode_family_bits,
        }
    }
}
