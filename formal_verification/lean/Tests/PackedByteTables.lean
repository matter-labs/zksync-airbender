import Airbender.Proofs.Tables.PackedByteTableChecks

namespace Tests.PackedByteTables
open Airbender.Setup Airbender.Setup.Proofs PackedWordBlocks
set_option warningAsError true

def descending : Code := .affine 2 1 (-1)
def crossing : Code := .dense 2 65536
def finalByte : Code := .affine 1 0 0
def chiByte : Code := .affine 1 1 0
def xorByte : Code := .affine 1 3 0
def highByte : Code := .affine 1 257 0

theorem and_checked : PackedByteTableChecks.check .bitAnd 257 [chiByte] = true := by decide +kernel
theorem or_checked : PackedByteTableChecks.check .bitOr 258 [xorByte] = true := by decide +kernel
theorem xor_checked : PackedByteTableChecks.check .bitXor 258 [xorByte] = true := by decide +kernel
theorem chi_checked : PackedByteTableChecks.check .chi 258 [chiByte] = true := by decide +kernel
theorem descending_checked : PackedByteTableChecks.check .chi 256 [descending] = true := by decide +kernel
theorem crossing_checked : PackedByteTableChecks.check .chi 255 [crossing] = true := by decide +kernel
theorem final_checked : PackedByteTableChecks.check .chi 65535 [finalByte] = true := by decide +kernel

theorem wrong_operation_rejected : PackedByteTableChecks.check .bitXor 258 [chiByte] = false := by decide +kernel
theorem high_byte_rejected : PackedByteTableChecks.check .chi 258 [highByte] = false := by decide +kernel
theorem wrong_stride_rejected : PackedByteTableChecks.check .chi 256 [.affine 2 1 1] = false := by decide +kernel
theorem outside_domain_rejected : PackedByteTableChecks.check .chi 65536 [finalByte] = false := by decide +kernel
theorem extra_window_rejected : PackedByteTableChecks.legal 0 513 = false := by decide +kernel

theorem original_chi : checkBlocks (fun index => (index % 256 ^^^ 255) &&& (index / 256)) 256
    [Block.affine 2 1 (-1)] = true :=
  PackedByteTableChecks.check_sound .chi 256 [descending] descending_checked

theorem source_binding : crossing.decode 65536 = Block.dense #[0, 1] := by decide +kernel

end Tests.PackedByteTables
