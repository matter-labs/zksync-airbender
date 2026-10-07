import Airbender.Review.AddSub.Theorems
import Airbender.Review.JumpBranchSlt.Theorems
import Airbender.Review.MulDiv.Theorems
import Airbender.Review.ShiftBinop.Theorems

#print axioms Airbender.AddSub.soundness
#print axioms Airbender.AddSub.babyBear_soundness
#print axioms Airbender.AddSub.Discarded.soundness
#print axioms Airbender.AddSub.Discarded.babyBear_soundness
#print axioms Airbender.AddSub.pc_successor
#print axioms Airbender.AddSub.babyBear_pc_successor
#print axioms Airbender.AddSub.local_flags
#print axioms Airbender.AddSub.delegation_zeroes
#print axioms Airbender.AddSub.compose
#print axioms Airbender.AddSub.timestamp_equations
#print axioms Airbender.AddSub.babyBear_timestamp_equations
#print axioms Airbender.AddSub.Modular.soundness
#print axioms Airbender.AddSub.NonDeterminism.write_soundness
#print axioms Airbender.AddSub.NonDeterminism.babyBear_write_soundness
#print axioms Airbender.AddSub.Proofs.modular_result
#print axioms Airbender.AddSub.Proofs.modular_canonical_output
#print axioms Airbender.Reference.RiscV.Sail.step_of_destination
#print axioms Airbender.Reference.RiscV.Sail.retire_of_destination
#print axioms Airbender.Reference.RiscV.Sail.retire_no_write
#print axioms Airbender.Reference.RiscV.Sail.compose_steps
#print axioms Airbender.Reference.RiscV.Sail.initialize_next_pc
#print axioms Airbender.Reference.RiscV.Sail.tick_pc_run
#print axioms Airbender.Reference.RiscV.Sail.spec_of_result
#print axioms Airbender.Reference.RiscV.Sail.spec_zero_write
#print axioms Airbender.Verification.assertion_of_holds
#print axioms Airbender.Verification.lookup_of_holds
#print axioms Airbender.Verification.range16Table
#print axioms Airbender.Verification.range16_bound
#print axioms Airbender.AddSub.Proofs.output_bounds
#print axioms Airbender.Artifact.signedCoefficient_cast
#print axioms Airbender.Reference.Sail.freeM_bind_assoc
#print axioms Airbender.Reference.Sail.interpret_bind

#print axioms Airbender.JumpBranchSlt.local_flags
#print axioms Airbender.JumpBranchSlt.local_ranges
#print axioms Airbender.JumpBranchSlt.timestamp_equations
#print axioms Airbender.JumpBranchSlt.babyBear_timestamp_equations
#print axioms Airbender.JumpBranchSlt.unsigned_borrow
#print axioms Airbender.JumpBranchSlt.unsigned_destination
#print axioms Airbender.JumpBranchSlt.Comparison.soundness
#print axioms Airbender.JumpBranchSlt.Comparison.babyBear_soundness
#print axioms Airbender.JumpBranchSlt.Proofs.comparison_pc
#print axioms Airbender.JumpBranchSlt.lookup_values
#print axioms Airbender.Verification.regIsZero_value
#print axioms Airbender.Verification.u16Sign_value
#print axioms Airbender.Verification.conditional_value
#print axioms Airbender.Verification.jumpCleanup_value
#print axioms Airbender.Arithmetic.Word.borrow_iff

#print axioms Airbender.JumpBranchSlt.signed_destination
#print axioms Airbender.JumpBranchSlt.branch_resolution
#print axioms Airbender.JumpBranchSlt.branch_pc
#print axioms Airbender.JumpBranchSlt.masked_destination
#print axioms Airbender.JumpBranchSlt.Proofs.subtraction_equations
#print axioms Airbender.JumpBranchSlt.Proofs.pc_carries
#print axioms Airbender.JumpBranchSlt.Proofs.resolution_key
#print axioms Airbender.Arithmetic.Word.signed_lt_iff

#print axioms Airbender.JumpBranchSlt.jump_link
#print axioms Airbender.JumpBranchSlt.jump_pc
#print axioms Airbender.JumpBranchSlt.Proofs.arithmetic_carries
#print axioms Airbender.Arithmetic.clear_low_bit_toNat

#print axioms Airbender.MulDiv.local_flags
#print axioms Airbender.MulDiv.local_ranges
#print axioms Airbender.MulDiv.byte_values
#print axioms Airbender.MulDiv.carry_bounds
#print axioms Airbender.MulDiv.divisor_zero_iff
#print axioms Airbender.MulDiv.division_by_zero
#print axioms Airbender.MulDiv.pc_successor
#print axioms Airbender.Verification.u16LowByte_value
#print axioms Airbender.Verification.range13_bound
#print axioms Airbender.MulDiv.soundness
#print axioms Airbender.MulDiv.babyBear_soundness
#print axioms Airbender.Arithmetic.product_of_columns
#print axioms Airbender.MulDiv.product_with_remainder

#print axioms Airbender.MulDiv.Proofs.remainder_lt_divisor
#print axioms Airbender.MulDiv.Proofs.division_nonzero
#print axioms Airbender.Reference.RiscV.Sail.truncate_nat
#print axioms Airbender.Reference.RiscV.Sail.truncate_int
#print axioms Airbender.Reference.RiscV.Sail.mul_low_signed
#print axioms Airbender.Reference.RiscV.Sail.mul_high_unsigned
#print axioms Airbender.MulDiv.Proofs.multiplication_result
#print axioms Airbender.ShiftBinop.local_flags
#print axioms Airbender.ShiftBinop.local_ranges
#print axioms Airbender.ShiftBinop.pc_successor
#print axioms Airbender.ShiftBinop.soundness
#print axioms Airbender.ShiftBinop.babyBear_soundness
#print axioms Airbender.Verification.binary_lookup
#print axioms Airbender.Arithmetic.bytes_value
