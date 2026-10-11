import Airbender.Proofs.UnifiedReduced.CustomDecoder
import Airbender.Proofs.UnifiedReduced.History

namespace Airbender.UnifiedReduced.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem custom_row_zero_preserving [Fact p.Prime] (hp : 524288 < p)
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    {entry : UnifiedReduced.ProgramEntry} (fields : customDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) :
    RowZeroPreserving (⟨.machine, w⟩ : Row p UnifiedFamily) := by
  intro port present zero reads
  simp [Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts] at present
  rcases present with rfl | rfl | rfl
  · exact reads _ (by simp [Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts]) le_rfl zero
  · exact reads _ (by simp [Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts]) le_rfl zero
  · have address : (w 29).val = 0 ∧ (w 44).val = 0 ∧ (w 45).val = 0 := by
      simpa [MemoryAddress.code, pairCode, Cell.addressCode, Nat.pair_eq_pair] using zero
    have noRAM : w 29 = 0 := by simpa using address.1
    have location := Verification.assertion_of_holds h ⟨31, by rw [constraint_count]; decide⟩
    simp [importedConstraints, FlatOperation.constraints, Expression.eval,
      Verification.environment, noRAM] at location
    have targetZero : w 7 = 0 := by
      have lo : w 44 = 0 := by simpa using address.2.1
      rw [lo] at location
      linear_combination -location
    have rd := congrArg (fun q : Vector (ZMod p) 9 => q[4]) query
    change w 7 = (entry.data.rd.toNat : ZMod p) at rd
    have originalZero : entry.data.rd = 0 := by
      have value := congrArg ZMod.val rd
      rw [targetZero, ZMod.val_zero, ZMod.val_natCast_of_lt (by have := entry.data.rd.isLt; omega)] at value
      exact BitVec.eq_of_toNat_eq value.symm
    exact False.elim (custom_field_nonzero fields originalZero)

theorem custom_zero_preserving [Fact p.Prime] (hp : 524288 < p) {trace : UnifiedTrace p}
    (accepted : Accepted trace) {before : State}
    {addresses : List (BitVec 32)} {program : List UnifiedReduced.ProgramEntry}
    (image : customProgramImage before addresses = some program) (decoded : Decoded trace program) :
    ZeroPreserving trace := by
  intro row member
  cases row with
  | mk family w =>
    cases family
    have core := Verification.holds_of_sublist (accepted.constraints ⟨.machine, w⟩ member)
      (List.sublist_append_left (importedConstraints trace.rom) importedConstraintsTimestampLookups)
    obtain ⟨entry, source, query, _⟩ := custom_fetched hp image core (decoded _ member)
    exact custom_row_zero_preserving hp core source.fields query

theorem custom_memory_execution [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : UnifiedTrace p}
    (accepted : Accepted trace) {before : State}
    {cells : List Cell} {program : List UnifiedReduced.ProgramEntry}
    (inputs : NativeInputs customDecoderFields trace before cells program) (decoded : Decoded trace program) :
    MemoryExecution trace before cells := by
  obtain ⟨addresses, image⟩ := inputs.programImage
  have zero := custom_zero_preserving (by dsimp [timestampBase] at hp; omega) accepted image decoded
  exact native_row_history hp inverse accepted inputs.clocks inputs.image inputs.distinct inputs.aligned
    (zero_writes_of_preserving hp inverse accepted inputs.clocks inputs.image zero)

theorem custom_row_position [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : UnifiedTrace p}
    (accepted : Accepted trace) {initial : State}
    {cells : List Cell} {program : List UnifiedReduced.ProgramEntry}
    (inputs : NativeInputs customDecoderFields trace initial cells program) (decoded : Decoded trace program)
    {row : Row p UnifiedFamily} {before : State}
    (position : RowPosition trace initial cells row before) :
    ∃ events after,
      SailHistory cells events (retiredState initial row.start.word.toBitVec) before ∧
      SailHistory cells (rowEvents trace.memoryEpoch row).reverse before after := by
  obtain ⟨history, rows, final, consistent, permutation, ordered, native, matched⟩ :=
    custom_memory_execution hp inverse accepted inputs decoded
  have projection :
      (rows.flatMap fun row => (rowEvents trace.memoryEpoch row).reverse).Perm trace.nativeEvents := by
    rw [native_events_projection hp inverse accepted inputs.clocks]
    exact permutation.flatMap (fun row _ => List.reverse_perm _)
  obtain ⟨events, rawBefore, rawAfter, _, past, current, state⟩ :=
    row_context_of_history permutation ordered native projection position
  subst before
  exact ⟨_, _, retired_state_history past _, retired_state_history current _⟩

theorem custom_row_position_exists [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : UnifiedTrace p}
    (accepted : Accepted trace) {initial : State}
    {cells : List Cell} {program : List UnifiedReduced.ProgramEntry}
    (inputs : NativeInputs customDecoderFields trace initial cells program) (decoded : Decoded trace program)
    {row : Row p UnifiedFamily} (member : row ∈ trace.rows) :
    ∃ before, RowPosition trace initial cells row before := by
  obtain ⟨history, rows, final, consistent, permutation, ordered, native, matched⟩ :=
    custom_memory_execution hp inverse accepted inputs decoded
  exact row_position_of_history permutation ordered native member

end Airbender.UnifiedReduced.Proofs
