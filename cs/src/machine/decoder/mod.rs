pub mod decode_optimized_must_handle_csr;

use super::*;
use crate::devices::risc_v_types::NUM_INSTRUCTION_TYPES;

// We will base our decoder on the following observations and limitations for now:
// - unsupported instructions == unsatisfiable circuit
// - UNIMP instruction (csrrw x0, cycle, x0) is checked before decoding by the main circuit, and leads to being unsatisiable
// - any CSR number check is done in CSRRW instruction, even though we can check 7-bit combinations
// - CSR writes are no-op effectively, as we only support non-determinism CSR and delegation via special CSR indexes
// - that means that CSRRWI and similar options do not need to be supported yet
// in this case we just need
// - 1 boolean to mark apriori-invalid instruction
// - 6 bits to decode instruction type, so we can assemble the immediate
// - immediates are always decoded as operand-2 for purposes of bit decomposition and sign splitting
// - some number of bits to decode "major" family type
// - some number of bits that are like a "scratch space" and each instruction interprets them as it wants

pub const NUM_INSTRUCTION_TYPES_IN_DECODE_BITS: usize = NUM_INSTRUCTION_TYPES;

pub struct DecoderInput<F: PrimeField> {
    pub instruction: Register<F>,
}
