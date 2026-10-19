import Tests.ControlComparisons
import Airbender.Review.Trace.Families.JumpBranchSlt.ComparisonExecution

namespace Tests.ComparisonExecution
open Airbender Trace Arithmetic Reference.RiscV.Sail Reference.Sail
open Tests.ControlComparisons

/-- The same four initialized native fixtures now execute their original
    public-decoded clauses from their actual public states, including retirement.
    The native history determines the cell state; no after-state is supplied. -/
theorem initialized_execution (kind : Kind) :
    ∃ entry ∈ setup.program, ∃ clause after,
      entry.SourceWith (before kind) JumpBranchSlt.decoderFields ∧
      JumpBranchSlt.decoderQuery (assignment kind) = entry.query ∧
      registerClause entry.instruction = some clause ∧
      SailHistory [.register 0,.register 1,.register 2,.register 3]
        (rowEvents (trace kind).memoryEpoch (nativeRow kind)).reverse (before kind) after ∧
      run (normalStep clause) (before kind) = .ok SailRV32.Functions.RETIRE_SUCCESS
        (retiredState after (BitVec.ofNat 32 (4 * kind.index + 4))) ∧
      run (SailRV32.Functions.get_arch_pc ())
        (retiredState after (BitVec.ofNat 32 (4 * kind.index + 4))) =
        .ok (BitVec.ofNat 32 (4 * kind.index + 4))
          (retiredState after (BitVec.ofNat 32 (4 * kind.index + 4))) := by
  have aligned : ∀ cell ∈ [Cell.register 0,.register 1,.register 2,.register 3], cell.Aligned := by
    intro cell member
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> simp [Cell.Aligned]
  obtain ⟨history,rows,after,_,permutation,_,_,_,segments⟩ :=
    JumpBranchSlt.public_comparison_execution (program_image kind) (public_inputs kind)
      (accepted kind) (decoded kind) aligned
  have singleton : rows = [nativeRow kind] :=
    List.perm_singleton.mp (by simpa only [trace] using permutation)
  obtain ⟨entry,member,rowBefore,rowAfter,clause,source,query,earlier,current,later,matched,retired⟩ :=
    segments [] (nativeRow kind) [] singleton (by cases kind <;> decide)
  change SailHistory _ [] (before kind) rowBefore at earlier
  change SailHistory _ [] rowAfter after at later
  cases earlier
  cases later
  have inputPC : (Word.mk (assignment kind 0).val (assignment kind 1).val).toBitVec =
      BitVec.ofNat 32 (4 * kind.index) := by cases kind <;> decide
  have outputPC : (Word.mk (assignment kind 13).val (assignment kind 14).val).toBitVec =
      BitVec.ofNat 32 (4 * kind.index + 4) := by cases kind <;> decide
  have pc : run (SailRV32.Functions.get_arch_pc ()) (before kind) =
      .ok (BitVec.ofNat 32 (4 * kind.index)) (before kind) := by
    apply read_register
    simp [before]
  change run (normalStep clause)
    (retiredState (before kind) (Word.mk (assignment kind 0).val (assignment kind 1).val).toBitVec) =
    .ok SailRV32.Functions.RETIRE_SUCCESS
      (retiredState after (Word.mk (assignment kind 13).val (assignment kind 14).val).toBitVec) at retired
  rw [inputPC,outputPC,Trace.Proofs.normal_step_rebased pc clause] at retired
  exact ⟨entry,member,clause,after,source,query,matched,current,retired,
    Trace.Proofs.retired_state_pc _ _⟩

/-- Original SLTIU reads public x1=123, compares it with sign-extended -1,
    discards its true result at x0 and retires PC eight to twelve. -/
theorem x0_retirement :
    run (SailRV32.Functions.rX_bits (.Regidx 1)) (before .sltiu0) =
      .ok (123 : BitVec 32) (before .sltiu0) ∧
    ∃ entry ∈ setup.program, ∃ clause,
      entry.SourceWith (before .sltiu0) JumpBranchSlt.decoderFields ∧
      JumpBranchSlt.decoderQuery (assignment .sltiu0) = entry.query ∧
      registerClause entry.instruction = some clause ∧
      run (normalStep clause) (before .sltiu0) = .ok SailRV32.Functions.RETIRE_SUCCESS
        (retiredState (before .sltiu0) 12) := by
  constructor
  · apply read_register
    simp [before,Kind.source,Kind.immediate,Std.ExtDHashMap.get?_insert]
  · obtain ⟨entry,member,clause,after,source,query,matched,history,retired,_⟩ :=
      initialized_execution .sltiu0
    have rd := (Trace.Proofs.native_query_indices (by decide : limbBase < mersenne31Modulus) query).2.2
    change 0 = entry.data.rd.toNat at rd
    have zero : entry.data.rd = 0 := BitVec.eq_of_toNat_eq (by simpa using rd.symm)
    have written := JumpBranchSlt.Proofs.history_register_write (by decide) (trace .sltiu0).memoryEpoch history query
    rw [zero] at written
    change run (SailRV32.Functions.wX_bits zeroRegister _) (before .sltiu0) = .ok () after at written
    rw [write_zero] at written
    have same : before .sltiu0 = after := (EStateM.Result.ok.inj written).2
    rw [← same] at retired
    exact ⟨entry,member,clause,source,query,matched,retired⟩

end Tests.ComparisonExecution
