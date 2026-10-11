import Airbender.Review.Delegation.CallerTheorems
import Airbender.Proofs.Sail.WordMemoryState
import Airbender.Proofs.Delegation.Requests
import Airbender.Proofs.BabyBear
import Airbender.Proofs.Trace.Timestamps

namespace Tests.DelegationCaller
open Airbender Delegation Trace Arithmetic Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

private def encoding (family : Delegation.Family) : BitVec 32 :=
  BitVec.ofNat 32 (Requests.csr family * 2 ^ 20 + 0x1073)

private def instruction (family : Delegation.Family) : SailRV32.instruction :=
  .CSRReg (BitVec.ofNat 12 (Requests.csr family), .Regidx 0, .Regidx 0, .CSRRW)

private def entry (family : Delegation.Family) : Caller.ProgramEntry :=
  ⟨0, encoding family, instruction family, ⟨family, 0, 0, 0, ⟨0, 0⟩, 128, 0⟩⟩

private theorem decoding (family : Delegation.Family) :
    SailRV32.Functions.encdec_backwards (encoding family) =
      (.pure (instruction family) : SailRV32.SailM SailRV32.instruction) := by
  cases family <;> dsimp only [encoding, instruction, Requests.csr]
  all_goals simp only [SailRV32.Functions.encdec_backwards,
    SailRV32.Functions.currentlyEnabled, SailRV32.Functions.hartSupports]
  all_goals rfl

theorem original_decoder (family : Delegation.Family) (state : State) :
    run (SailRV32.Functions.encdec_backwards (encoding family)) state =
      .ok (instruction family) state := by
  rw [decoding]
  rfl

theorem metadata (family : Delegation.Family) :
    Caller.decoderFields (instruction family) = some (entry family).data := by
  cases family <;> rfl

private def assignment (family : Delegation.Family) (column : Nat) : ZMod babyBearModulus :=
  if column = 2 ∨ column = 19 then 4
  else if column = 21 then 8
  else if column = 4 ∨ column = 17 ∨ column = 42 ∨ column = 43 ∨ column = 44 then 1
  else if column = 6 then Requests.csr family else 0

theorem satisfies (family : Delegation.Family) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (assignment family))
      AddSub.clockConstraints := by
  apply Verification.holds_append
  · rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
    constructor
    · cases family <;> decide +kernel
    · rw [List.forall_mem_iff_forall_getElem]
      intro i bound
      have short : i < 6 := by simpa only [AddSub.lookup_count] using bound
      interval_cases i
      all_goals apply Verification.range16_contains
      all_goals cases family <;> decide +kernel
  · rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
    constructor
    · simp [AddSub.importedConstraintsTimestampLookups, FlatOperation.constraints]
    · rw [List.forall_mem_iff_forall_getElem]
      intro i bound
      have short : i < 8 := by simpa only [AddSub.timestamp_count] using bound
      interval_cases i
      all_goals apply Trace.Proofs.range_contains
      all_goals cases family <;> decide +kernel

theorem query_bound (family : Delegation.Family) :
    Caller.nativeQuery (assignment family) = Caller.query (entry family) := by
  cases family <;> decide +kernel

theorem request_address (family : Delegation.Family) :
    (Requests.caller (assignment family)).csr = Requests.csr family ∧
      31 < (Requests.caller (assignment family)).csr := by
  cases family <;> decide +kernel

theorem unsupported_rejected :
    Caller.decoderFields (.CSRReg (0x7C7, .Regidx 1, .Regidx 0, .CSRRW)) = none ∧
    Caller.decoderFields (.CSRReg (0x7C7, .Regidx 0, .Regidx 1, .CSRRW)) = none ∧
    Caller.decoderFields (.CSRReg (0x7C0, .Regidx 0, .Regidx 0, .CSRRW)) = none := by
  decide +kernel

private def before (family : Delegation.Family) : State :=
  wordWriteState default 0 (encoding family)

theorem public_image (family : Delegation.Family) :
    Caller.programImage (before family) [0] = some [entry family] := by
  have bytes : (Cell.ram 0).read (before family) = .ok (encoding family) (before family) :=
    written_word_read default 0 (encoding family)
  have decoded := original_decoder family (before family)
  have fields := metadata family
  simp only [List.mapM_cons, List.mapM_nil, programEntryRunWith, bytes, decoded, fields,
    bind, Option.bind, pure]
  rfl

theorem public_caller (family : Delegation.Family) :
    Caller.Binding (assignment family) (before family) [entry family] := by
  apply Caller.soundness (by decide)
  · exact Verification.holds_of_sublist (satisfies family)
      (List.sublist_append_left _ AddSub.importedConstraintsTimestampLookups)
  · exact public_image family
  · change ∃ i : Fin 1, Caller.nativeQuery (assignment family) =
      Caller.query ([entry family].get i)
    exact ⟨0, query_bound family⟩

theorem truncated_csr_rejected (family : Delegation.Family) :
    ¬ (Caller.decoderTable [entry family]).Contains #[]
      (Caller.nativeQuery (fun column => if column = 6 then 0 else assignment family column)) := by
  intro member
  change ∃ i : Fin 1, Caller.nativeQuery
    (fun column => if column = 6 then 0 else assignment family column) =
    Caller.query ([entry family].get i) at member
  obtain ⟨i, equal⟩ := member
  have index : i = 0 := Subsingleton.elim _ _
  subst i
  have address := Caller.Proofs.query_csr (by decide) equal
  change 0 = Requests.csr family at address
  cases family <;> norm_num [Requests.csr] at address

end Tests.DelegationCaller
