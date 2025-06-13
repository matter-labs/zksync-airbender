use super::*;

pub const CSR_COMMON_OP_KEY: DecoderMajorInstructionFamilyKey =
    DecoderMajorInstructionFamilyKey("CSR_COMMON_KEY");
pub const CSSRW_OP_KEY: DecoderInstructionVariantsKey =
    DecoderInstructionVariantsKey("CSRRW/CSRRWI");
pub const CSSRC_OP_KEY: DecoderInstructionVariantsKey =
    DecoderInstructionVariantsKey("CSRRC/CSRRCI");
pub const CSSRS_OP_KEY: DecoderInstructionVariantsKey =
    DecoderInstructionVariantsKey("CSRRS/CSRRSI");

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CsrOp<
    const SUPPORT_CSRRC: bool,
    const SUPPORT_CSRRS: bool,
    const SUPPORT_CSR_IMMEDIATES: bool,
>;

impl<const SUPPORT_CSRRC: bool, const SUPPORT_CSRRS: bool, const SUPPORT_CSR_IMMEDIATES: bool>
    DecodableMachineOp for CsrOp<SUPPORT_CSRRC, SUPPORT_CSRRS, SUPPORT_CSR_IMMEDIATES>
{
    fn define_decoder_subspace(
        &self,
        opcode: u8,
        func3: u8,
        func7: u8,
    ) -> Result<
        (
            InstructionType,
            DecoderMajorInstructionFamilyKey,
            &'static [DecoderInstructionVariantsKey],
        ),
        (),
    > {
        let params = match (opcode, func3, func7) {
            (OPERATION_SYSTEM, 0b001, _) => {
                // CSRRW
                (
                    InstructionType::IType,
                    CSR_COMMON_OP_KEY,
                    &[CSSRW_OP_KEY][..],
                )
            }
            (OPERATION_SYSTEM, 0b101, _) if SUPPORT_CSR_IMMEDIATES => {
                // CSRRWI
                (
                    InstructionType::IType,
                    CSR_COMMON_OP_KEY,
                    &[CSSRW_OP_KEY][..],
                )
            }
            (OPERATION_SYSTEM, 0b011, _) if SUPPORT_CSRRC => {
                // CSRRC
                (
                    InstructionType::IType,
                    CSR_COMMON_OP_KEY,
                    &[CSSRC_OP_KEY][..],
                )
            }
            (OPERATION_SYSTEM, 0b111, _) if SUPPORT_CSRRC && SUPPORT_CSR_IMMEDIATES => {
                // CSRRCI
                (
                    InstructionType::IType,
                    CSR_COMMON_OP_KEY,
                    &[CSSRC_OP_KEY][..],
                )
            }
            (OPERATION_SYSTEM, 0b010, _) if SUPPORT_CSRRS => {
                // CSRRS
                (
                    InstructionType::IType,
                    CSR_COMMON_OP_KEY,
                    &[CSSRS_OP_KEY][..],
                )
            }
            (OPERATION_SYSTEM, 0b110, _) if SUPPORT_CSRRS && SUPPORT_CSR_IMMEDIATES => {
                // CSRRSI
                (
                    InstructionType::IType,
                    CSR_COMMON_OP_KEY,
                    &[CSSRS_OP_KEY][..],
                )
            }
            _ => return Err(()),
        };

        Ok(params)
    }
}
