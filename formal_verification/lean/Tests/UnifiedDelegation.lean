import Tests.DelegationCaller
import Tests.BigintMemory
import Airbender.Review.UnifiedReduced.Theorems
import Airbender.Review.UnifiedReduced.Setup

namespace Tests.UnifiedDelegation
open Airbender Trace Arithmetic Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

private def before (family : Delegation.Family) : State :=
  wordWriteState Tests.BigintMemory.before 0 (Tests.DelegationCaller.entry family).bits

private def assignmentWith (address : ZMod babyBearModulus) (column : Nat) : ZMod babyBearModulus :=
  if column = 2 ∨ column = 30 then 4
  else if column = 32 then 8
  else if column = 4 ∨ column = 18 ∨ column = 129 ∨ column = 130 ∨
      column = 131 ∨ column = 132 ∨ column = 133 then 1
  else if column = 6 ∨ column = 38 then address else 0

private def assignment (family : Delegation.Family) := assignmentWith (Delegation.Requests.csr family)

private theorem public_image (family : Delegation.Family) :
    UnifiedReduced.Caller.programImage (before family) [0] = some [Tests.DelegationCaller.entry family] := by
  have bytes : (Cell.ram 0).read (before family) =
      .ok (Tests.DelegationCaller.entry family).bits (before family) :=
    written_word_read Tests.BigintMemory.before 0 (Tests.DelegationCaller.entry family).bits
  have decoded : run (SailRV32.Functions.encdec_backwards (Tests.DelegationCaller.entry family).bits)
      (before family) = .ok (Tests.DelegationCaller.entry family).instruction (before family) :=
    Tests.DelegationCaller.original_decoder family _
  have fields : Delegation.Caller.decoderFields (Tests.DelegationCaller.entry family).instruction =
      some (Tests.DelegationCaller.entry family).data := Tests.DelegationCaller.metadata family
  simp only [UnifiedReduced.Caller.programImage, Delegation.Caller.programImage,
    programImageRunWith, List.mapM_cons, List.mapM_nil, programEntryRunWith,
    bytes, decoded, fields, bind, Option.bind, pure]
  rfl

private theorem generic_core (state : State) (address : ZMod babyBearModulus) (addressBound : address.val < limbBase) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (assignmentWith address))
    (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table state)) := by
  simp [UnifiedReduced.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Verification.environment, Expression.eval, assignmentWith, Lookup.Contains, Table.toRaw, fromElements]
  repeat' apply And.intro
  all_goals solve
    | decide +kernel
    | (apply Verification.range16_contains
       simpa [Expression.eval, assignmentWith] using addressBound)
    | (apply Verification.range16_contains
       simp [Expression.eval, assignmentWith]
       decide +kernel)
    | (refine ⟨(0 : Fin 2097537), ?_⟩
       change (#v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : Vector (ZMod babyBearModulus) 10) =
         (UnifiedReduced.Setup.fixedRow (0 : Fin 1048961)).map (fun (n : Nat) => (n : ZMod babyBearModulus))
       decide +kernel)

private theorem core (family : Delegation.Family) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (assignment family))
    (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table (before family))) :=
  generic_core (before family) _ (by cases family <;> decide +kernel)

private theorem timestamps (family : Delegation.Family) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (assignment family)) UnifiedReduced.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i bound
    have short : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals cases family <;> decide +kernel

theorem all_caller_forms_satisfy (family : Delegation.Family) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (assignment family))
    (UnifiedReduced.clockConstraints (UnifiedReduced.Setup.table (before family))) :=
  Verification.holds_append (core family) (timestamps family)

theorem original_public_caller_soundness (family : Delegation.Family) :
    UnifiedReduced.Caller.Binding (assignment family) (before family) [Tests.DelegationCaller.entry family] := by
  apply UnifiedReduced.Caller.soundness (by decide +kernel) (core family) (public_image family)
  change ∃ i : Fin 1, UnifiedReduced.decoderQuery (assignment family) =
    Delegation.Caller.query ([Tests.DelegationCaller.entry family].get i)
  refine ⟨0, ?_⟩
  cases family <;> decide +kernel

theorem caller_request_retains_full_csr (family : Delegation.Family) :
    (UnifiedReduced.Caller.request (assignment family)).csr = Delegation.Requests.csr family ∧
    31 < (UnifiedReduced.Caller.request (assignment family)).csr := by
  cases family <;> decide +kernel

private def truncated (family : Delegation.Family) := assignmentWith (Delegation.Requests.csr family % 32)

theorem truncated_csr_locally_satisfies (family : Delegation.Family) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (truncated family))
      (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table (before family))) :=
  generic_core (before family) _ (by cases family <;> decide +kernel)

theorem truncated_csr_rejected_by_public_decoder (family : Delegation.Family) :
    ¬ (UnifiedReduced.Caller.decoderTable (p := babyBearModulus) [Tests.DelegationCaller.entry family]).Contains
      #[] (UnifiedReduced.decoderQuery (truncated family)) := by
  change ¬ ∃ i : Fin 1, UnifiedReduced.decoderQuery (truncated family) =
    Delegation.Caller.query ([Tests.DelegationCaller.entry family].get i)
  intro ⟨i, equal⟩
  have field := congrArg (fun q : Vector (ZMod babyBearModulus) 9 => q[3]) equal
  fin_cases i
  have impossible : ¬ (UnifiedReduced.decoderQuery (truncated family))[3] =
      (Delegation.Caller.query ([Tests.DelegationCaller.entry family].get 0))[3] := by
    cases family <;> decide +kernel
  exact impossible field

end Tests.UnifiedDelegation
