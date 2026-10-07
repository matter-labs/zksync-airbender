import Airbender.Proofs.UnifiedReduced
import Airbender.Review.SubwordMemory.Theorems
import Airbender.Proofs.SubwordMemory.Stores
import Airbender.Proofs.WordMemory
import Airbender.Review.AddSub.Theorems
import Airbender.Proofs.AddSub.Timestamp
import Airbender.Proofs.AddSub.Selectors
import Airbender.Review.JumpBranchSlt.Theorems
import Airbender.Review.MulDiv.Theorems
import Airbender.Review.ShiftBinop.Theorems
import Airbender.Proofs.ShiftBinop.Shifts
import Airbender.Proofs.Sail.Runtime
import Airbender.Review.WordMemory.Theorems

#print axioms Airbender.WordMemory.soundness
#print axioms Airbender.WordMemory.babyBear_soundness
#print axioms Airbender.WordMemory.variable_roles
#print axioms Airbender.Reference.RiscV.Sail.retire_with_memory
#print axioms Airbender.Reference.RiscV.Sail.load_word
#print axioms Airbender.Reference.RiscV.Sail.store_word
#print axioms Airbender.Reference.RiscV.Sail.write_word_frame
#print axioms Airbender.Reference.RiscV.Sail.writeMemory
#print axioms SailRV32.Functions.execute_LOAD
#print axioms SailRV32.Functions.execute_STORE
#print axioms Sail.ArchSem.plat_term_write
#print axioms Sail.ArchSem.load_reservation
#print axioms Sail.ArchSem.match_reservation

#print axioms Sail.ArchSem.runtimeErrors
#print axioms Airbender.Reference.Sail.early_return_error
#print axioms Airbender.Reference.Sail.early_return_catch

#print axioms Airbender.AddSub.soundness
#print axioms Airbender.AddSub.babyBear_soundness
#print axioms Airbender.AddSub.Discarded.soundness
#print axioms Airbender.AddSub.Discarded.babyBear_soundness
#print axioms Airbender.AddSub.Proofs.pc_successor
#print axioms Airbender.AddSub.Proofs.local_flags
#print axioms Airbender.AddSub.Proofs.delegation_zeroes
#print axioms Airbender.Reference.RiscV.Sail.compose
#print axioms Airbender.AddSub.Proofs.timestamp_equations
#print axioms Airbender.AddSub.Modular.soundness
#print axioms Airbender.AddSub.NonDeterminism.write_soundness
#print axioms Airbender.AddSub.NonDeterminism.babyBear_write_soundness
#print axioms Airbender.AddSub.Proofs.modular_result
#print axioms Airbender.AddSub.Proofs.modular_canonical_output
#print axioms Airbender.Reference.RiscV.Sail.step_of_destination
#print axioms Airbender.Reference.RiscV.Sail.retire_of_destination
#print axioms Airbender.Reference.RiscV.Sail.retire_of_effects
#print axioms Airbender.Reference.Sail.early_return_lift_bind
#print axioms Airbender.Reference.RiscV.Sail.jump_to_aligned
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

#print axioms Airbender.JumpBranchSlt.Proofs.local_flags
#print axioms Airbender.JumpBranchSlt.variable_roles
#print axioms Airbender.JumpBranchSlt.Proofs.local_ranges
#print axioms Airbender.JumpBranchSlt.Proofs.timestamp_equations
#print axioms Airbender.JumpBranchSlt.Proofs.unsigned_borrow
#print axioms Airbender.JumpBranchSlt.Proofs.unsigned_destination
#print axioms Airbender.JumpBranchSlt.Comparison.soundness
#print axioms Airbender.JumpBranchSlt.Comparison.babyBear_soundness
#print axioms Airbender.JumpBranchSlt.Proofs.comparison_pc
#print axioms Airbender.JumpBranchSlt.Proofs.lookup_values
#print axioms Airbender.Verification.regIsZero_value
#print axioms Airbender.Verification.u16Sign_value
#print axioms Airbender.Verification.conditional_value
#print axioms Airbender.Verification.jumpCleanup_value
#print axioms Airbender.Arithmetic.Word.borrow_iff

#print axioms Airbender.JumpBranchSlt.Proofs.signed_destination
#print axioms Airbender.JumpBranchSlt.Proofs.branch_resolution
#print axioms Airbender.JumpBranchSlt.Proofs.branch_pc
#print axioms Airbender.JumpBranchSlt.Branch.soundness
#print axioms Airbender.JumpBranchSlt.Branch.babyBear_soundness
#print axioms SailRV32.Functions.execute_BTYPE
#print axioms SailRV32.Functions.execute_JAL
#print axioms SailRV32.Functions.execute_JALR
#print axioms Sail.ArchSem.sys_enable_experimental_extensions
#print axioms Airbender.JumpBranchSlt.Proofs.masked_destination
#print axioms Airbender.JumpBranchSlt.Proofs.subtraction_equations
#print axioms Airbender.JumpBranchSlt.Proofs.pc_carries
#print axioms Airbender.JumpBranchSlt.Proofs.resolution_key
#print axioms Airbender.Arithmetic.Word.signed_lt_iff

#print axioms Airbender.JumpBranchSlt.Proofs.jump_link
#print axioms Airbender.JumpBranchSlt.Proofs.jump_pc
#print axioms Airbender.JumpBranchSlt.Jump.soundness
#print axioms Airbender.JumpBranchSlt.Jump.babyBear_soundness
#print axioms Airbender.Reference.RiscV.Sail.landing_pad_disabled
#print axioms Airbender.Reference.RiscV.Sail.clear_bit_zero
#print axioms Airbender.JumpBranchSlt.Proofs.arithmetic_carries
#print axioms Airbender.Arithmetic.clear_low_bit_toNat

#print axioms Airbender.MulDiv.Proofs.local_flags
#print axioms Airbender.MulDiv.Proofs.local_ranges
#print axioms Airbender.MulDiv.Proofs.byte_values
#print axioms Airbender.MulDiv.Proofs.carry_bounds
#print axioms Airbender.MulDiv.Proofs.divisor_zero_iff
#print axioms Airbender.MulDiv.Proofs.division_by_zero
#print axioms Airbender.MulDiv.Proofs.pc_successor
#print axioms Airbender.Verification.u16LowByte_value
#print axioms Airbender.Verification.range13_bound
#print axioms Airbender.MulDiv.soundness
#print axioms Airbender.MulDiv.babyBear_soundness
#print axioms Airbender.Arithmetic.product_of_columns
#print axioms Airbender.MulDiv.Proofs.product_with_remainder

#print axioms Airbender.MulDiv.Proofs.remainder_lt_divisor
#print axioms Airbender.MulDiv.Proofs.division_nonzero
#print axioms Airbender.Reference.RiscV.Sail.truncate_nat
#print axioms Airbender.Reference.RiscV.Sail.truncate_int
#print axioms Airbender.Reference.RiscV.Sail.mul_low_signed
#print axioms Airbender.Reference.RiscV.Sail.mul_high_unsigned
#print axioms Airbender.MulDiv.Proofs.multiplication_result
#print axioms Airbender.ShiftBinop.Proofs.local_flags
#print axioms Airbender.ShiftBinop.Proofs.local_ranges
#print axioms Airbender.ShiftBinop.Proofs.pc_successor
#print axioms Airbender.ShiftBinop.soundness
#print axioms Airbender.ShiftBinop.babyBear_soundness
#print axioms Airbender.Verification.binary_lookup
#print axioms Airbender.Arithmetic.bytes_value

#print axioms Airbender.Arithmetic.or_eq_add_of_disjoint
#print axioms Airbender.Arithmetic.chunks_disjoint
#print axioms Airbender.Arithmetic.chunks_or
#print axioms Airbender.Arithmetic.mapped_chunks_value
#print axioms Airbender.Verification.tagged_lookup_row
#print axioms Airbender.Verification.truncation_lookup
#print axioms Airbender.Verification.shift_lookup
#print axioms Airbender.Verification.shift_contributions_value
#print axioms Airbender.Verification.low_byte_shift_amount
#print axioms Airbender.ShiftBinop.Proofs.shift_amount
#print axioms Airbender.ShiftBinop.Proofs.shift_bytes
#print axioms Airbender.ShiftBinop.Proofs.shift_destination
#print axioms SailRV32.Functions.execute_SHIFTIOP

#print axioms SailRV32.Functions.execute_RTYPE
#print axioms SailRV32.Functions.execute_ITYPE

#print axioms Airbender.Reference.Sail.rev8_bytes
#print axioms Airbender.Reference.Sail.rev8_value
#print axioms SailRV32.Functions.execute_REV8

#print axioms Airbender.WordMemory.Proofs.local_flags
#print axioms Airbender.WordMemory.Proofs.local_ranges
#print axioms Airbender.WordMemory.Proofs.pc_successor
#print axioms Airbender.WordMemory.Proofs.effective_address
#print axioms Airbender.WordMemory.Proofs.register_address
#print axioms Airbender.WordMemory.Proofs.rom_selection
#print axioms Airbender.WordMemory.Proofs.data_lookup
#print axioms Airbender.WordMemory.Proofs.ram_data
#print axioms Airbender.WordMemory.Proofs.rom_data

#print axioms Airbender.SubwordMemory.variable_roles
#print axioms Airbender.SubwordMemory.Proofs.local_flags
#print axioms Airbender.SubwordMemory.Proofs.local_ranges
#print axioms Airbender.SubwordMemory.Proofs.pc_successor
#print axioms Airbender.SubwordMemory.Proofs.register_address
#print axioms Airbender.SubwordMemory.Proofs.aligned_address
#print axioms Airbender.SubwordMemory.Proofs.halfword_aligned
#print axioms Airbender.SubwordMemory.Proofs.effective_address
#print axioms Airbender.SubwordMemory.Proofs.rom_selection
#print axioms Airbender.SubwordMemory.Proofs.clearing_query
#print axioms Airbender.SubwordMemory.Proofs.data_query
#print axioms Airbender.SubwordMemory.Proofs.ram_load_query
#print axioms Airbender.SubwordMemory.Proofs.rom_load_query
#print axioms Airbender.SubwordMemory.Proofs.store_query
#print axioms Airbender.Arithmetic.range_separator
#print axioms Airbender.Reference.RiscV.Sail.load
#print axioms Airbender.Reference.RiscV.Sail.write_memory_frame

#print axioms Airbender.Verification.subwordRow
#print axioms Airbender.Verification.subwordTable
#print axioms Airbender.Verification.subword_ram_values
#print axioms Airbender.Verification.extend_subword_limbs
#print axioms Airbender.Verification.subword_load_extension
#print axioms Airbender.Verification.subword_ram_extension
#print axioms Airbender.SubwordMemory.Proofs.ram_output_bounds
#print axioms Airbender.Verification.subword_packed_extension
#print axioms Airbender.Verification.subword_extract
#print axioms Airbender.Reference.RiscV.Sail.read_subword
#print axioms Airbender.SubwordMemory.Proofs.ram_load_data
#print axioms Airbender.SubwordMemory.soundness
#print axioms Airbender.SubwordMemory.babyBear_soundness
#print axioms Airbender.Verification.subwordStoreContribution
#print axioms Airbender.Verification.subword_store_values
#print axioms Airbender.Verification.subword_zero_values
#print axioms Airbender.Verification.subword_store_contribution_bound
#print axioms Airbender.Verification.subword_store_entry
#print axioms Airbender.Verification.subword_store_packed
#print axioms Airbender.SubwordMemory.Proofs.clearing_data
#print axioms Airbender.SubwordMemory.Proofs.store_contribution
#print axioms Airbender.SubwordMemory.Proofs.store_data
#print axioms Airbender.Reference.RiscV.Sail.store_subword

#print axioms Airbender.SubwordMemory.Proofs.store_byte_encoding
#print axioms Airbender.Reference.RiscV.Sail.read_word_memory
#print axioms Airbender.Reference.RiscV.Sail.write_subword_cell
#print axioms Airbender.Reference.RiscV.Sail.write_subword_memory

#print axioms Airbender.Verification.subword_rom_result
#print axioms Airbender.SubwordMemory.Proofs.rom_load_data

#print axioms Airbender.Arithmetic.boolean_sum_le_one
#print axioms Airbender.UnifiedReduced.variable_roles
#print axioms Airbender.UnifiedReduced.Proofs.local_flags
#print axioms Airbender.UnifiedReduced.Proofs.dispatch_count
#print axioms Airbender.UnifiedReduced.Proofs.pc_bounds
#print axioms Airbender.UnifiedReduced.Proofs.pc_successor
