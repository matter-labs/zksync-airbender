import Airbender.Proofs.FullUnsigned.CPUWriteRules
import Airbender.Proofs.VerifierBoundary

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
variable [Fact babyBearModulus.Prime]

/-- Public full-width queries and state matching bound both native PC endpoints. -/
theorem unrolled_full_pc_bounds
    {initial : State} {text : List (BitVec 32)} {capacity : Nat}
    {masks : PooledFamily → NativeDecoder.ProgramRows.Mask}
    {columns : PooledFamily → List (List (ZMod babyBearModulus))}
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {extraSteps : List (MemoryToken babyBearModulus × MemoryToken babyBearModulus)}
    {extraRequests : List (Delegation.Requests.Request babyBearModulus)}
    (setup : UnrolledProgramSetup .fullUnsigned initial text capacity masks columns)
    (lookup : UnrolledDecoderExactLookup trace masks columns)
    (accepted : UnrolledAcceptance trace workers extraSteps extraRequests)
    (excluded : FullUnsigned.NoSpecial5Call initial text)
    (initialPC : trace.initial.word.lo < limbBase)
    (closure : VerifierBoundary.BootClosure trace.initial
      (trace.rows.map Row.start) (trace.rows.map Row.finish)) :
    ∀ row ∈ trace.rows, row.start.word.Bounded ∧ row.finish.word.Bounded := by
  have incoming : ∀ row ∈ trace.rows, row.start.word.Bounded := by
    intro row member
    rcases unrolled_full_native_row_classification setup lookup accepted excluded initialPC row member with
      ⟨entry, _, _, _, query, _⟩ | ⟨entry, _, _, family, query, _⟩ |
      ⟨entry, _, _, family, query, _⟩
    · have word := native_query_pc_word (by decide) query
      change row.start.word = Word.ofBitVec entry.pc at word
      exact word.symm ▸ Word.ofBitVec_bound entry.pc
    · have word := Delegation.Caller.Proofs.query_pc (by decide) query
      cases row with
      | mk kind w =>
        cases family
        change (Word.mk (w 0).val (w 1).val).Bounded
        change Word.mk (w 0).val (w 1).val = Word.ofBitVec entry.pc at word
        exact word.symm ▸ Word.ofBitVec_bound entry.pc
    · have low := congrArg (fun values : Vector (ZMod babyBearModulus) 9 => values[0]) query
      have high := congrArg (fun values : Vector (ZMod babyBearModulus) 9 => values[1]) query
      change row.assignment 0 = (Word.ofBitVec entry.pc).lo at low
      change row.assignment 1 = (Word.ofBitVec entry.pc).hi at high
      cases row with
      | mk kind w =>
        cases family
        change (w 0).val < limbBase ∧ (w 1).val < limbBase
        change w 0 = ((Word.ofBitVec entry.pc).lo : ZMod babyBearModulus) at low
        change w 1 = ((Word.ofBitVec entry.pc).hi : ZMod babyBearModulus) at high
        have bound := Word.ofBitVec_bound entry.pc
        rw [low, high, ZMod.val_natCast_of_lt (lt_trans bound.1 (by decide)),
          ZMod.val_natCast_of_lt (lt_trans bound.2 (by decide))]
        exact bound
  have terminal := VerifierBoundary.Proofs.terminal_bound (by decide : limbBase < babyBearModulus)
    accepted.states (VerifierBoundary.Proofs.boot_closure closure)
  intro row member
  refine ⟨incoming row member, ?_⟩
  have endpoint : row.finish ∈ trace.terminal :: trace.rows.map Row.start :=
    accepted.states.mem_iff.mp (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨row, member, rfl⟩))
  rcases List.mem_cons.mp endpoint with same | next
  · exact same ▸ terminal
  · obtain ⟨other, included, same⟩ := List.mem_map.mp next
    exact same ▸ incoming other included

end Airbender.Compiler.MachineTargets.Proofs
