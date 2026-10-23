import Mathlib.Algebra.EuclideanDomain.Field
import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Circuits.UnifiedReduced.Delegation
import Airbender.Proofs.UnifiedReduced.Decoder
import Airbender.Proofs.Delegation.CallerPC

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Arithmetic Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem caller_selectors [Fact p.Prime] (hp : FieldCapacity.NoWrap p 524288)
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p} {entry : ProgramEntry}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (query : decoderQuery w = Delegation.Caller.query entry) :
    ∀ i : Fin 19, w importedConstraintsDecoderColumns.flags[i] = if i.val = 7 then 1 else 0 := by
  let bits (i : Fin 19) := w importedConstraintsDecoderColumns.flags[i]
  have boolean : ∀ i, bits i = 0 ∨ bits i = 1 := by
    intro i
    have flag := UnifiedReduced.Proofs.local_flags h ⟨i.val + 1, by omega⟩
    fin_cases i <;> simpa [bits, importedConstraintsDecoderColumns] using flag
  have packed := congrArg (fun q : Vector (ZMod p) 9 => q[8]) query
  change (∑ i : Fin 19, (2 ^ i.val : Nat) * bits i) = (128 : ZMod p) at packed
  have recovered := Trace.Proofs.unpack_decoder_bits_general (by simpa using hp)
    (show 128 < 2 ^ 19 by decide) boolean packed
  intro i
  have bit := recovered i
  have value : (128 : Nat).testBit i.val = decide (i.val = 7) := by fin_cases i <;> decide
  simpa [bits, value] using bit

theorem caller_zeroes [Fact p.Prime] {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (selected : w 18 = 1) :
    w 42 = 0 ∧ w 43 = 0 ∧ w 40 = 0 ∧ w 41 = 0 ∧ w 50 = 0 ∧ w 51 = 0 := by
  have eq6 := Verification.assertion_of_holds h ⟨6, by rw [constraint_count]; decide⟩
  have eq7 := Verification.assertion_of_holds h ⟨7, by rw [constraint_count]; decide⟩
  have eq8 := Verification.assertion_of_holds h ⟨8, by rw [constraint_count]; decide⟩
  have eq9 := Verification.assertion_of_holds h ⟨9, by rw [constraint_count]; decide⟩
  have eq10 := Verification.assertion_of_holds h ⟨10, by rw [constraint_count]; decide⟩
  have eq11 := Verification.assertion_of_holds h ⟨11, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, selected] at eq6 eq7 eq8 eq9 eq10 eq11
  exact ⟨eq6, eq7, eq8, eq9, eq10, eq11⟩

theorem caller_binding [Fact p.Prime] (hp : FieldCapacity.NoWrap p 524288)
    {setup : Table (ZMod p) (fields 10)} {w : Nat → ZMod p}
    {before : State} {addresses : List (BitVec 32)} {program : List ProgramEntry}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup))
    (image : programImage before addresses = some program)
    (member : (decoderTable program).Contains #[] (decoderQuery w)) : Binding w before program := by
  change ∃ i : Fin program.length, decoderQuery w = Delegation.Caller.query (program.get i) at member
  obtain ⟨i, query⟩ := member
  let entry := program.get i
  have present : entry ∈ program := List.get_mem _ _
  have source := Trace.Proofs.run_program_sources image entry present
  have selectors := caller_selectors hp h query
  have s11 : w 11 = 0 := selectors 0
  have s12 : w 12 = 0 := selectors 1
  have s13 : w 13 = 0 := selectors 2
  have s14 : w 14 = 0 := selectors 3
  have s15 : w 15 = 0 := selectors 4
  have s16 : w 16 = 0 := selectors 5
  have s17 : w 17 = 0 := selectors 6
  have s18 : w 18 = 1 := selectors 7
  have s19 : w 19 = 0 := selectors 8
  have s20 : w 20 = 0 := selectors 9
  have s21 : w 21 = 0 := selectors 10
  have s22 : w 22 = 0 := selectors 11
  have s23 : w 23 = 0 := selectors 12
  have s24 : w 24 = 0 := selectors 13
  have s25 : w 25 = 0 := selectors 14
  have s26 : w 26 = 0 := selectors 15
  have s27 : w 27 = 0 := selectors 16
  have s28 : w 28 = 0 := selectors 17
  have s29 : w 29 = 0 := selectors 18
  have disabled := Verification.assertion_of_holds h ⟨92, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29] at disabled
  have active : w 4 = 1 := by linear_combination -disabled
  have csr := congrArg (fun fields : Vector (ZMod p) 9 => fields[3]) query
  change w 6 = (Delegation.Requests.csr entry.data.family : ZMod p) at csr
  have csrBound : Delegation.Requests.csr entry.data.family < p := by
    cases entry.data.family <;> simp only [Delegation.Requests.csr] <;> omega
  have requestCSR : (request w).csr = Delegation.Requests.csr entry.data.family := by
    change (w 6).val = _
    rw [csr, ZMod.val_natCast_of_lt csrBound]
  have rs1 := congrArg (fun fields : Vector (ZMod p) 9 => fields[2]) query
  have rd := congrArg (fun fields : Vector (ZMod p) 9 => fields[4]) query
  change w 5 = 0 at rs1
  change w 7 = 0 at rd
  have a29 := Verification.assertion_of_holds h ⟨29, by rw [constraint_count]; decide⟩
  have a30 := Verification.assertion_of_holds h ⟨30, by rw [constraint_count]; decide⟩
  have a31 := Verification.assertion_of_holds h ⟨31, by rw [constraint_count]; decide⟩
  have a32 := Verification.assertion_of_holds h ⟨32, by rw [constraint_count]; decide⟩
  simp [importedConstraints, FlatOperation.constraints, Expression.eval,
    Verification.environment, s28, s29, rd] at a29 a30 a31 a32
  have memread : w 38 = w 6 := by linear_combination a29
  have memreadHi : w 39 = 0 := a30
  have memwrite : w 44 = 0 := a31
  have memwriteHi : w 45 = 0 := a32
  obtain ⟨lo, hi, timeLo, timeHi, outLo, outHi⟩ := caller_zeroes h s18
  have initial : initialPC w = Word.ofBitVec entry.pc := by
    have low := congrArg (fun fields : Vector (ZMod p) 9 => fields[0]) query
    have high := congrArg (fun fields : Vector (ZMod p) 9 => fields[1]) query
    change w 0 = ((Word.ofBitVec entry.pc).lo : ZMod p) at low
    change w 1 = ((Word.ofBitVec entry.pc).hi : ZMod p) at high
    have bound := Word.ofBitVec_bound entry.pc
    have lo : (w 0).val = (Word.ofBitVec entry.pc).lo := by
      rw [low, ZMod.val_natCast_of_lt (by have := bound.1; dsimp [limbBase] at this; omega)]
    have hi : (w 1).val = (Word.ofBitVec entry.pc).hi := by
      rw [high, ZMod.val_natCast_of_lt (by have := bound.2; dsimp [limbBase] at this; omega)]
    exact congrArg₂ Word.mk lo hi
  have initialBounds : (initialPC w).Bounded := initial.symm ▸ Word.ofBitVec_bound entry.pc
  have mapping : w 0 = ((initialPC w).lo : ZMod p) ∧ w 1 = ((initialPC w).hi : ZMod p) ∧
      (finalPC w).lo = (w 30).val ∧ (finalPC w).hi = (w 31).val :=
    ⟨(ZMod.natCast_zmod_val _).symm, (ZMod.natCast_zmod_val _).symm, rfl, rfl⟩
  have pc := UnifiedReduced.Proofs.pc_successor (by omega) h active ⟨s21, s22, s23, s24⟩ mapping initialBounds
  have zero : (destinationToken w).word = ⟨0, 0⟩ := by
    simp [destinationToken, writeToken, MemoryToken.word, MemoryPort.writeCode,
      WordColumns.code, WordColumns.evaluate, importedConstraintsMemoryPorts, outLo, outHi]
  refine ⟨⟨entry, present, source, requestCSR⟩, ⟨active, s18⟩, ?_, ?_,
    ⟨initialBounds, UnifiedReduced.Proofs.pc_bounds h, pc.2.2⟩, ?_⟩
  · simp [virtualPort, importedConstraintsMemoryPorts, importedConstraintsTraceColumns,
      request, Delegation.Requests.caller, Delegation.Requests.callerPort,
      AddSub.importedConstraintsTraceColumns, AddSub.importedConstraintsDecoderColumns,
      AddSub.importedConstraintsMemoryPorts, Delegation.Requests.Request.empty,
      Delegation.Requests.Request.issued, Delegation.Requests.Request.token, readToken,
      writeToken, MemoryAddress.code, MemoryPort.readCode, MemoryPort.writeCode,
      WordColumns.code, WordColumns.evaluate, pairCode, rawPair, lo, hi, timeLo, timeHi,
      s28, memread, memreadHi]
    decide
  · refine ⟨?_, ?_, zero⟩
    · simp [sourceToken, readToken, importedConstraintsMemoryPorts, MemoryAddress.code,
        Cell.addressCode, rs1]
    · simp [destinationToken, writeToken, importedConstraintsMemoryPorts, MemoryAddress.code,
        pairCode, Cell.addressCode, s29, memwrite, memwriteHi]
  · intro state
    refine ⟨rfl, ?_, ?_⟩
    · rw [zero]
      change run (SailRV32.Functions.wX_bits zeroRegister 0) state = .ok () state
      rw [write_zero]
      rfl
    · intro read
      have prepare := initialize_next_pc read
      rw [run_bind_of_ok _ _ _ _ _ prepare]
      have finish := tick_pc_run (state := { state with regs := state.regs.insert .nextPC ((initialPC w).toBitVec + 4) })
        (pc := (initialPC w).toBitVec + 4) (by simp)
      simpa only [pc.2.2] using finish

end Airbender.UnifiedReduced.Caller.Proofs
