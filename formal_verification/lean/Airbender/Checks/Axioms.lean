import Airbender
import Tests.PC
import Tests.CircuitRows
import Tests.Timestamps
import Tests.NativeClocks

#print axioms Airbender.AddSub.soundness
#print axioms Airbender.AddSub.mersenne31_soundness
#print axioms Airbender.AddSub.Proofs.constraint_count
#print axioms Airbender.AddSub.Proofs.lookup_count
#print axioms Airbender.AddSub.Proofs.selected_bits
#print axioms Airbender.AddSub.Proofs.carry_bits
#print axioms Airbender.AddSub.Proofs.output_columns
#print axioms Airbender.AddSub.Proofs.output_bounds
#print axioms Airbender.AddSub.Proofs.result_of_limbs
#print axioms Airbender.AddSub.Proofs.result_word
#print axioms Airbender.AddSub.Proofs.pc_successor
#print axioms Airbender.AddSub.Proofs.soundness
#print axioms Airbender.Artifact.signedCoefficient_mod
#print axioms Airbender.Artifact.signedCoefficient_cast
#print axioms Airbender.Artifact.serialized_modulus_is_zero
#print axioms Airbender.Verification.holds_of_sublist
#print axioms Airbender.Verification.holds_append
#print axioms Airbender.Verification.assertion_of_holds
#print axioms Airbender.Verification.lookup_of_holds
#print axioms Airbender.Verification.range16_bound
#print axioms Airbender.Verification.range16_contains
#print axioms Airbender.Verification.timestamp19_bound
#print axioms Airbender.Verification.timestamp19_contains
#print axioms Tests.AddSub.add_satisfies
#print axioms Tests.AddSub.add_execution
#print axioms Tests.AddSub.changed_write_rejected
#print axioms Tests.PC.wrap_satisfies
#print axioms Tests.PC.native_pc_wrap
#print axioms Tests.CircuitRows.addi_carry_satisfies
#print axioms Tests.CircuitRows.sub_borrow_satisfies
#print axioms Tests.CircuitRows.lui_satisfies
#print axioms Tests.CircuitRows.auipc_satisfies
#print axioms Tests.CircuitRows.discarded_write_satisfies
#print axioms Tests.Timestamps.wrong_borrow_rejected
#print axioms Tests.Timestamps.wrong_decoder_mask_rejected
#print axioms Airbender.AddSub.Proofs.clock_columns
#print axioms Airbender.AddSub.Proofs.memory_ports
#print axioms Airbender.AddSub.Proofs.timestamp_equations
#print axioms Airbender.AddSub.Proofs.clock_effects
#print axioms Airbender.Trace.Proofs.increment
#print axioms Airbender.Trace.Proofs.comparison_of_room
#print axioms Airbender.Trace.Proofs.comparison
#print axioms Airbender.Trace.Proofs.native_port_order_of_room
#print axioms Airbender.Trace.Proofs.distinct_slots
#print axioms Airbender.Trace.Proofs.native_port_order
#print axioms Airbender.Trace.Proofs.clock_effects
#print axioms Tests.NativeClocks.native_order
#print axioms Tests.NativeClocks.native_clock_advances
#print axioms Airbender.Trace.WordColumns.code_u16
#print axioms Airbender.Trace.WordColumns.evaluate_u16
