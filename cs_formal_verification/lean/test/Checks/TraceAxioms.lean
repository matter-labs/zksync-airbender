import Tests.PooledHistory
import Tests.PooledROM

import Tests.SubwordMemoryTimestamp
import Tests.ShiftBinopTimestamp
import Tests.ShiftBinopHistory
import Tests.ShiftBinopPorts
import Tests.ShiftBinopImmediate
import Slop.Trace.BytePorts
import Tests.MulDivTimestamp
import Tests.BranchTrace
import Tests.ComparisonTrace
import Tests.JalrTrace
import Slop.Trace.Claims
import Slop.Trace.ClockHistory
import Tests.Timestamps
import Tests.TraceHistory
import Tests.TraceMemory
import Tests.TraceExecution
import Tests.NativeROM
import Tests.NonDeterminismDecoder
import Tests.OracleTrace
import Tests.PooledOracle
import Tests.JumpTimestamp
import Tests.JumpPorts
import Tests.JumpHistory
import Tests.JumpSailHistory
import Tests.DiscardedLoad
import Tests.TraceROM
import Tests.TraceStore
import Tests.SailHistory
import Tests.TraceZeroRegister
import Slop.Trace.MemoryPorts
import Human.Helpers.Core.Configuration

#print axioms Airbender.Trace.timestampTable
#print axioms Airbender.Trace.ROMView.shadow
#print axioms Airbender.Trace.ROMView.nativeBootImage
#print axioms Airbender.Trace.ROMView.read_data_unused
#print axioms Tests.NativeROM.native_constraints
#print axioms Tests.NativeROM.native_accepted
#print axioms Tests.NativeROM.physical_bytes_are_not_native_seed
#print axioms Airbender.Trace.Proofs.ordered_row_boundaries
#print axioms Airbender.Reference.RiscV.Sail.Configured
#print axioms Airbender.Trace.Proofs.range_bound
#print axioms Airbender.Trace.Proofs.range_contains
#print axioms Airbender.Trace.Proofs.increment
#print axioms Airbender.Trace.Proofs.comparison
#print axioms Airbender.Trace.Proofs.distinct_slots
#print axioms Airbender.Trace.Proofs.incoming_bounds
#print axioms Airbender.Trace.Proofs.incoming_alignment
#print axioms Airbender.Trace.Proofs.low_alignment
#print axioms Airbender.Trace.Proofs.terminal_clock
#print axioms Airbender.AddSub.clockConstraints
#print axioms Airbender.AddSub.timestamp_count
#print axioms Airbender.AddSub.clock_columns
#print axioms Airbender.WordMemory.clockConstraints
#print axioms Airbender.WordMemory.timestamp_count
#print axioms Airbender.WordMemory.clock_columns
#print axioms Airbender.Trace.Proofs.addSub_clock
#print axioms Airbender.Trace.Proofs.wordMemory_clock
#print axioms Tests.Timestamps.normal_effects
#print axioms Tests.Timestamps.rollover_effects
#print axioms Tests.Timestamps.equal_previous_rejected
#print axioms Tests.Timestamps.oversized_limb_rejected
#print axioms Airbender.AddSub.memory_ports
#print axioms Airbender.AddSub.memory_clocks
#print axioms Airbender.WordMemory.memory_ports
#print axioms Airbender.WordMemory.memory_clocks
#print axioms Airbender.Trace.Proofs.pairCode_eq_iff
#print axioms Airbender.Trace.Proofs.readonly_preserves_value
#print axioms Airbender.Trace.Proofs.mixed_register
#print axioms Airbender.Trace.Proofs.mixed_ram
#print axioms Airbender.Trace.Proofs.ram_register_disjoint
#print axioms Airbender.Trace.Accepted
#print axioms Airbender.Trace.Row.reads
#print axioms Airbender.Trace.Row.writes
#print axioms Airbender.Trace.Proofs.addSub_final_bound
#print axioms Airbender.Trace.Proofs.addSub_step
#print axioms Airbender.Trace.Proofs.wordMemory_final_bound
#print axioms Airbender.Trace.Proofs.wordMemory_step
#print axioms Airbender.Trace.Proofs.write_time
#print axioms Airbender.Trace.Proofs.clock_inputs
#print axioms Airbender.Trace.Proofs.trace_clocks
#print axioms Airbender.Trace.Proofs.trace_terminal_clock
#print axioms Airbender.Trace.clocks
#print axioms Airbender.Trace.terminal_clock
#print axioms Tests.TraceHistory.local_satisfies
#print axioms Tests.TraceHistory.accepted
#print axioms Tests.TraceHistory.derived_clock
#print axioms Tests.TraceHistory.terminal_eight
#print axioms Tests.TraceHistory.unmatched_previous_rejected
#print axioms Airbender.Trace.Proofs.matched_flow
#print axioms Airbender.Trace.Proofs.increasing_acyclic
#print axioms Airbender.Trace.Proofs.rank_unique
#print axioms Airbender.Trace.Proofs.matched_path
#print axioms Airbender.Trace.Proofs.native_state_path
#print axioms Airbender.Trace.Proofs.row_clocks_unique
#print axioms Airbender.Trace.Proofs.slots_unique
#print axioms Airbender.Trace.Proofs.access_times_unique
#print axioms Airbender.Trace.state_path
#print axioms Airbender.Trace.unique_access_times
#print axioms Tests.TraceHistory.complete_state_path
#print axioms Tests.TraceHistory.unique_slots
#print axioms Tests.TraceHistory.reordered_path
#print axioms Airbender.Trace.Proofs.ports_clocks
#print axioms Airbender.Trace.Proofs.port_offset
#print axioms Airbender.Trace.Proofs.initialized_addresses
#print axioms Airbender.Trace.initialized_addresses
#print axioms Tests.TraceHistory.initialized_ports
#print axioms Airbender.Trace.Proofs.rank_ordered
#print axioms Airbender.Trace.Proofs.boundary_keys
#print axioms Airbender.Trace.Proofs.keyed_paths
#print axioms Airbender.Trace.Proofs.keyed_paths_finite
#print axioms Airbender.Trace.Proofs.native_memory_paths
#print axioms Airbender.Trace.memory_paths
#print axioms Tests.TraceHistory.complete_memory_paths
#print axioms Tests.TraceHistory.interleaved_memory_paths
#print axioms Airbender.Trace.Proofs.consecutive_ranks
#print axioms Airbender.Trace.Proofs.latest_reads
#print axioms Airbender.Trace.latest_reads
#print axioms Tests.TraceHistory.latest_values
#print axioms Tests.TraceHistory.changed_value_locally_valid
#print axioms Tests.TraceHistory.changed_read_value_rejected
#print axioms Airbender.Trace.Proofs.cell_history
#print axioms Airbender.Trace.Proofs.transfer_event
#print axioms Airbender.Trace.Proofs.native_cell_histories
#print axioms Airbender.Trace.cell_histories
#print axioms Tests.TraceMemory.local_satisfies
#print axioms Tests.TraceMemory.accepted
#print axioms Tests.TraceMemory.nonzero_clean_histories
#print axioms Airbender.AddSub.Proofs.written_limb_bounds
#print axioms Airbender.Trace.MemoryToken.word
#print axioms Airbender.Trace.ValueBoundary
#print axioms Airbender.Trace.Proofs.earlier_write
#print axioms Airbender.Trace.Proofs.read_word
#print axioms Airbender.Trace.Proofs.write_source
#print axioms Airbender.Trace.Proofs.read_bounds
#print axioms Airbender.Trace.Proofs.write_bounds
#print axioms Airbender.Trace.Proofs.terminal_bounds
#print axioms Airbender.Trace.read_bounds
#print axioms Airbender.Trace.terminal_bounds
#print axioms Tests.TraceMemory.bounded_native_values
#print axioms Airbender.Arithmetic.Word.ofBitVec
#print axioms Airbender.Arithmetic.Word.ofBitVec_bound
#print axioms Airbender.Arithmetic.Word.ofBitVec_value
#print axioms Airbender.Arithmetic.Word.ofBitVec_roundtrip
#print axioms Airbender.Trace.Cell.addressCode
#print axioms Airbender.Trace.Cell.initialToken
#print axioms Airbender.Trace.Proofs.initial_token_word
#print axioms Airbender.Trace.Proofs.cell_address_injective
#print axioms Airbender.PCState.State.word
#print axioms Airbender.AddSub.decoder_columns
#print axioms Airbender.WordMemory.decoder_columns
#print axioms Airbender.Trace.Row.decoderColumns
#print axioms Airbender.Trace.Row.decoderQuery
#print axioms Airbender.Trace.Proofs.unpack_decoder_bits
#print axioms Airbender.Trace.Proofs.cell_address_bound
#print axioms Airbender.Trace.Proofs.address_word
#print axioms Tests.TraceMemory.noncanonical_ram_rejected
#print axioms Airbender.Trace.ROM.rows
#print axioms Airbender.Trace.ROM.table
#print axioms Tests.TraceROM.native_query
#print axioms Tests.TraceROM.wrong_value_rejected
#print axioms Tests.TraceROM.missing_address_rejected
#print axioms Airbender.Trace.Data.memoryEpoch
#print axioms Airbender.Trace.Data.nativeEvents
#print axioms Airbender.Trace.Data.memoryEvents
#print axioms Airbender.Trace.MemoryHistory
#print axioms Airbender.Trace.Proofs.key_filter_singleton
#print axioms Airbender.Trace.Proofs.consistent_retime
#print axioms Airbender.Trace.Proofs.memory_event_times_unique
#print axioms Airbender.Trace.Proofs.native_memory_history
#print axioms Airbender.Trace.memory_history
#print axioms Tests.TraceMemory.merged_clean_history
#print axioms Tests.TraceMemory.second_satisfies
#print axioms Tests.TraceMemory.two_accepted
#print axioms Tests.TraceMemory.reordered_memory_history
#print axioms Tests.TraceStore.local_satisfies
#print axioms Tests.TraceStore.accepted
#print axioms Airbender.Trace.Cell.Aligned
#print axioms Airbender.Trace.memoryWord
#print axioms Airbender.Trace.Proofs.below_epoch
#print axioms Airbender.Trace.Proofs.native_history_parts
#print axioms Airbender.AddSub.Proofs.zero_operands_result
#print axioms Tests.TraceZeroRegister.local_satisfies
#print axioms Tests.TraceZeroRegister.accepted
#print axioms Tests.TraceZeroRegister.nonzero_native_output_rejected
#print axioms Airbender.Trace.Proofs.memory_steps_matched
#print axioms Airbender.Trace.Proofs.memory_steps_address
#print axioms Airbender.Trace.Proofs.memory_steps_increase
#print axioms Airbender.Trace.Proofs.terminal_latest_value
#print axioms Tests.TraceStore.fabricated_terminal_value_rejected
#print axioms Airbender.Trace.Proofs.native_events_projection
#print axioms Airbender.Trace.Proofs.native_row_order
#print axioms Tests.TraceMemory.reordered_instruction_accesses
#print axioms Airbender.Trace.Proofs.zip_fst_sublist
#print axioms Airbender.Trace.Proofs.ordered_row_state_path

#print axioms Tests.NonDeterminismDecoder.native_constraints

#print axioms Airbender.Trace.NonDeterminism.Proofs.read_index_permutation
#print axioms Airbender.Trace.NonDeterminism.Proofs.ordered_consumption
#print axioms Airbender.Trace.NonDeterminism.Proofs.native_consumption
#print axioms Airbender.Trace.NonDeterminism.native_consumption
#print axioms Tests.NonDeterminismDecoder.single_native_consumption
#print axioms Tests.NonDeterminismDecoder.clock_positions
#print axioms Tests.NonDeterminismDecoder.ordered_responses
#print axioms Tests.NonDeterminismDecoder.storage_order_does_not_change_position
#print axioms Tests.NonDeterminismDecoder.chronological_ports
#print axioms Tests.NonDeterminismDecoder.swapped_stream_rejected
#print axioms Tests.NonDeterminismDecoder.short_stream_rejected



#print axioms Airbender.Trace.NonDeterminism.readCount
#print axioms Airbender.Trace.NonDeterminism.Proofs.consumed_length
#print axioms Tests.OracleTrace.short_stream_rejected
#print axioms Tests.OracleTrace.wrong_response_rejected

#print axioms Airbender.Trace.Proofs.native_port_order
#print axioms Airbender.Trace.Proofs.clock_effects
#print axioms Airbender.JumpBranchSlt.timestamp_count
#print axioms Airbender.JumpBranchSlt.clock_columns
#print axioms Airbender.JumpBranchSlt.memory_ports
#print axioms Airbender.JumpBranchSlt.decoder_columns
#print axioms Airbender.JumpBranchSlt.Proofs.timestamp_equations
#print axioms Airbender.JumpBranchSlt.Proofs.final_clock_bound
#print axioms Airbender.JumpBranchSlt.Proofs.clocks
#print axioms Airbender.JumpBranchSlt.clocks
#print axioms Tests.JumpTimestamp.checked_clocks
#print axioms Tests.JumpTimestamp.incorrect_borrow_rejected

#print axioms Airbender.Trace.nativeDecoderQuery
#print axioms Airbender.Trace.Proofs.unpack_decoder_bits_of_width


#print axioms Airbender.Trace.nativeRowEvents

#print axioms Tests.JumpHistory.constraints
#print axioms Tests.JumpHistory.accepted
#print axioms Tests.JumpHistory.derived_clocks
#print axioms Tests.JumpHistory.complete_state_path
#print axioms Tests.JumpHistory.complete_memory_history
#print axioms Tests.JumpHistory.latest_native_reads
#print axioms Tests.JumpHistory.invented_old_destination_rejected


#print axioms Airbender.Trace.Proofs.outgoing_pc_bounds

#print axioms Airbender.Trace.Proofs.read_bounds_of_sources
#print axioms Airbender.Trace.Proofs.write_bounds_of_sources
#print axioms Airbender.Trace.Proofs.terminal_bounds_of_sources

#print axioms Airbender.Trace.Proofs.matched_incoming_property
#print axioms Airbender.JumpBranchSlt.Proofs.outgoing_pc_aligned
#print axioms Airbender.JumpBranchSlt.Proofs.trace_pc_alignment
#print axioms Tests.JumpSailHistory.decoded_pc_alignment



#print axioms Airbender.Arithmetic.Word.eq_zero_of_bounded





#print axioms Airbender.MulDiv.clock_columns
#print axioms Airbender.MulDiv.memory_ports
#print axioms Airbender.MulDiv.decoder_columns
#print axioms Airbender.MulDiv.Proofs.timestamp_equations
#print axioms Airbender.MulDiv.Proofs.final_clock_bound
#print axioms Airbender.MulDiv.Proofs.clocks
#print axioms Airbender.MulDiv.Proofs.nativeClockLaws
#print axioms Airbender.MulDiv.clocks
#print axioms Tests.MulDivTimestamp.constraints
#print axioms Tests.MulDivTimestamp.native_clocks


#print axioms Airbender.MulDiv.Proofs.outgoing_pc_bounds
#print axioms Airbender.MulDiv.Proofs.write_sources




#print axioms Airbender.Trace.Proofs.packed_bytes
#print axioms Airbender.Trace.Proofs.byte_port_code
#print axioms Airbender.ShiftBinop.clock_columns
#print axioms Airbender.ShiftBinop.memory_ports
#print axioms Airbender.ShiftBinop.decoder_columns
#print axioms Airbender.ShiftBinop.Proofs.timestamp_equations
#print axioms Airbender.ShiftBinop.Proofs.final_clock_bound
#print axioms Airbender.ShiftBinop.Proofs.clocks
#print axioms Airbender.ShiftBinop.Proofs.nativeClockLaws
#print axioms Tests.ShiftBinop.satisfies
#print axioms Tests.ShiftBinopTimestamp.constraints
#print axioms Tests.ShiftBinopTimestamp.native_clocks
#print axioms Airbender.ShiftBinop.clocks

#print axioms Airbender.Trace.Proofs.byte_port_bytes
#print axioms Airbender.Trace.Proofs.byte_port_low_bytes
#print axioms Airbender.ShiftBinop.Proofs.outgoing_pc_bounds
#print axioms Airbender.ShiftBinop.Proofs.binary_query_values
#print axioms Airbender.ShiftBinop.Proofs.shift_source_bounds
#print axioms Airbender.ShiftBinop.Proofs.binary_written_bounds
#print axioms Airbender.ShiftBinop.Proofs.binary_left_bytes
#print axioms Airbender.ShiftBinop.Proofs.shift_left_bytes
#print axioms Airbender.ShiftBinop.Proofs.shift_right_low_byte
#print axioms Tests.ShiftBinopPorts.constraints
#print axioms Tests.ShiftBinopPorts.unused_high_bytes
#print axioms Airbender.Verification.binary_sign_lookup
#print axioms Airbender.Trace.Proofs.packed_bytes_unique
#print axioms Airbender.Arithmetic.sign_extend_high_bytes
#print axioms Airbender.ShiftBinop.Proofs.binary_sign_byte
#print axioms Airbender.ShiftBinop.Proofs.binary_register_right_bytes
#print axioms Airbender.ShiftBinop.Proofs.binary_immediate_right_bytes
#print axioms Tests.ShiftBinopImmediate.constraints
#print axioms Airbender.Verification.shift_contribution_halves
#print axioms Airbender.ShiftBinop.Proofs.shift_output_sums
#print axioms Airbender.ShiftBinop.Proofs.shift_destination_limbs
#print axioms Airbender.ShiftBinop.Proofs.shift_written_bounds
#print axioms Tests.ShiftBinopPorts.written_bounds
#print axioms Airbender.SubwordMemory.timestamp_count
#print axioms Airbender.SubwordMemory.clock_columns
#print axioms Airbender.SubwordMemory.memory_ports
#print axioms Airbender.SubwordMemory.memory_clocks
#print axioms Airbender.SubwordMemory.decoder_columns
#print axioms Airbender.SubwordMemory.Proofs.timestamp_equations
#print axioms Airbender.SubwordMemory.Proofs.final_clock_bound
#print axioms Airbender.SubwordMemory.Proofs.clocks
#print axioms Airbender.SubwordMemory.Proofs.nativeClockLaws
#print axioms Airbender.SubwordMemory.clocks
#print axioms Tests.SubwordMemoryTimestamp.constraints
#print axioms Tests.SubwordMemoryTimestamp.native_clocks
#print axioms Airbender.SubwordMemory.Proofs.outgoing_pc_bounds
#print axioms Airbender.Trace.Proofs.WriteBoundsFromReads
#print axioms Airbender.Trace.Proofs.write_rules_of_sources
#print axioms Airbender.Trace.Proofs.read_bounds_of_rules
#print axioms Airbender.Trace.Proofs.write_bounds_of_rules
#print axioms Airbender.Trace.Proofs.terminal_bounds_of_rules
#print axioms Airbender.Verification.subword_rom_bounds
#print axioms Airbender.SubwordMemory.Proofs.write_rules
#print axioms Airbender.SubwordMemory.Proofs.native_value_bounds
#print axioms Airbender.Trace.Proofs.pooledClockLaws
#print axioms Tests.PooledHistory.local_add
#print axioms Tests.PooledHistory.accepted
#print axioms Tests.PooledHistory.derived_clocks
#print axioms Tests.PooledHistory.latest_reads
#print axioms Tests.PooledHistory.fabricated_read_rejected

#print axioms Airbender.Trace.Proofs.row_write_rule_of_sources










#print axioms Airbender.Trace.Proofs.row_write_values






#print axioms Airbender.Trace.ExternalStream.index
#print axioms Airbender.Trace.ExternalStream.count
#print axioms Airbender.Trace.ExternalStream.Ports
#print axioms Airbender.Trace.ExternalStream.consumed
#print axioms Airbender.Trace.ExternalStream.Proofs.consumed_length
#print axioms Airbender.Trace.ExternalStream.Proofs.ordered_consumption
#print axioms Airbender.Trace.ExternalStream.Proofs.native_consumption
#print axioms Airbender.Trace.NonDeterminism.Pooled.isRead
#print axioms Airbender.Trace.NonDeterminism.Pooled.response
#print axioms Airbender.Trace.NonDeterminism.Pooled.readIndex
#print axioms Airbender.Trace.NonDeterminism.Pooled.readCount
#print axioms Airbender.Trace.NonDeterminism.Pooled.StreamPorts
#print axioms Airbender.Trace.NonDeterminism.Pooled.consumed
#print axioms Airbender.Trace.NonDeterminism.Pooled.Proofs.read_index_permutation
#print axioms Airbender.Trace.NonDeterminism.Pooled.Proofs.consumed_length
#print axioms Airbender.Trace.NonDeterminism.Pooled.Proofs.native_consumption
#print axioms Airbender.Trace.NonDeterminism.Pooled.native_consumption
#print axioms Tests.PooledOracle.foreign_selector_ignored





