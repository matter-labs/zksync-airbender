import Airbender
import Tests.PC
import Tests.CircuitRows
import Tests.Timestamps
import Tests.NativeClocks
import Tests.InitializedHistory
import Tests.NativeDecoderMetadata
import Tests.DecoderSetup

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

#print axioms Airbender.AddSub.Proofs.final_clock_bound
#print axioms Airbender.AddSub.Proofs.clock_advance
#print axioms Airbender.Trace.Proofs.clock_inputs
#print axioms Airbender.Trace.Proofs.trace_clocks
#print axioms Airbender.Trace.Proofs.native_state_path
#print axioms Airbender.Trace.Proofs.access_times_unique
#print axioms Airbender.Trace.Proofs.native_memory_paths
#print axioms Airbender.Trace.Proofs.initialized_addresses
#print axioms Airbender.Trace.Proofs.latest_reads
#print axioms Airbender.Trace.Proofs.native_cell_histories
#print axioms Airbender.Trace.Proofs.native_memory_history
#print axioms Airbender.Trace.native_memory_soundness
#print axioms Tests.InitializedHistory.complete_history
#print axioms Tests.InitializedHistory.destination_latest
#print axioms Tests.InitializedHistory.stale_local_satisfies
#print axioms Tests.InitializedHistory.stale_history_rejected

#print axioms Airbender.AddSub.Proofs.memory_clocks

#print axioms Airbender.PCState.Proofs.encoded_bounds
#print axioms Airbender.Trace.Proofs.cell_read_frame
#print axioms Airbender.Trace.Proofs.initial_token_word
#print axioms Airbender.Trace.Proofs.image_reads
#print axioms Airbender.Trace.Proofs.image_sources
#print axioms Airbender.Trace.Proofs.image_addresses
#print axioms Airbender.Trace.Proofs.image_cell_source
#print axioms Airbender.Trace.Proofs.image_bounds
#print axioms Airbender.Trace.Proofs.image_clocks
#print axioms Airbender.Trace.Proofs.cell_address_injective
#print axioms Airbender.Trace.Proofs.image_unique
#print axioms Airbender.Trace.Proofs.initial_state_source
#print axioms Airbender.Trace.Proofs.initial_pc_bound
#print axioms Airbender.Trace.Proofs.initial_state_pc
#print axioms Airbender.Trace.Proofs.image_clock_boundary
#print axioms Airbender.Trace.public_image_memory_soundness
#print axioms Tests.InitializedHistory.public_image_history
#print axioms Tests.InitializedHistory.missing_register_rejected
#print axioms Tests.InitializedHistory.missing_bytes_rejected

#print axioms Airbender.AddSub.Proofs.decoder_columns
#print axioms Tests.NativeDecoderMetadata.query_order
#print axioms Tests.CircuitRows.x0_sub_satisfies
#print axioms Tests.CircuitRows.x0_sub_execution

#print axioms Airbender.AddSub.Proofs.packed_mask_bound
#print axioms Airbender.AddSub.Proofs.written_limb_bounds
#print axioms Airbender.Trace.Proofs.entry_source
#print axioms Airbender.Trace.Proofs.program_sources
#print axioms Airbender.Trace.Proofs.decoder_field_bounds
#print axioms Airbender.Trace.Proofs.word_of_pc_query
#print axioms Airbender.Trace.Proofs.native_query_pc_word
#print axioms Airbender.Trace.Proofs.native_query_immediate_word
#print axioms Airbender.Trace.Proofs.padding_excluded
#print axioms Airbender.Trace.Proofs.decoder_member
#print axioms Airbender.Trace.Proofs.setup_sources
#print axioms Airbender.Trace.Proofs.decoded_sources
#print axioms Airbender.Trace.Proofs.decoded_zero_flag
#print axioms Airbender.Trace.Proofs.decoded_word_bounds
#print axioms Airbender.Trace.Proofs.read_bounds_of_sources
#print axioms Airbender.Trace.Proofs.write_bounds_of_sources
#print axioms Airbender.Trace.Proofs.terminal_bounds_of_sources
#print axioms Airbender.Trace.Proofs.row_write_source
#print axioms Airbender.Trace.Proofs.decoded_write_sources
#print axioms Airbender.Trace.public_decoder_soundness
#print axioms Airbender.Trace.public_image_value_bounds
#print axioms Tests.InitializedHistory.setup_built
#print axioms Tests.InitializedHistory.padding_retained
#print axioms Tests.InitializedHistory.native_padding_rejected
#print axioms Tests.InitializedHistory.public_decode_source
#print axioms Tests.InitializedHistory.decoder_word_bounds
#print axioms Tests.InitializedHistory.initialized_read_bounds
#print axioms Tests.InitializedHistory.initialized_terminal_bounds
#print axioms Tests.InitializedHistory.setup_capacity_rejected
#print axioms Tests.InitializedHistory.bad_flag_local_satisfies
#print axioms Tests.InitializedHistory.bad_flag_write_unbounded
#print axioms Tests.InitializedHistory.bad_flag_decoder_rejected
#print axioms Tests.DecoderSetup.upper_funct3
#print axioms Tests.DecoderSetup.negative_immediate
#print axioms Tests.DecoderSetup.x0_retains_sub

#print axioms Airbender.Trace.Proofs.image_value_bounds
