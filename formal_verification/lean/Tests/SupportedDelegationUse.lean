import Airbender.Review.Trace.UnifiedReduced.DelegationUse
import Airbender.Proofs.Arithmetic.Word

namespace Tests.SupportedDelegationUse
open Airbender Airbender.Arithmetic Airbender.Trace Airbender.UnifiedReduced.Caller
open Airbender.UnifiedReduced.Caller.DelegationUse
open Airbender.Reference.RiscV.Sail
set_option warningAsError true

theorem bigint_zero_rejected : ¬ ControlAt .bigint 0 0 := by
  rintro ⟨⟨opcode, carry⟩, same⟩
  fin_cases opcode <;> cases carry <;> exact absurd same (by decide)

theorem bigint_high_control_rejected : ¬ ControlAt .bigint 0 65537 := by
  rintro ⟨⟨opcode, carry⟩, same⟩
  fin_cases opcode <;> cases carry <;> exact absurd same (by decide)

theorem bigint_add_supported : ControlAt .bigint 0 1 :=
  ⟨⟨0, false⟩, rfl⟩

theorem g_full_entry_supported : ControlAt (.g false) 0 0 := rfl
theorem g_reduced_entry_supported : ControlAt (.g true) 0 128 := rfl

theorem round_full_entry_supported : ControlAt (.round false) 0 524288 :=
  ⟨0, by decide, rfl⟩

theorem round_nonzero_low_rejected (reduced : Bool) (index : Nat) :
    ¬ ControlAt (.round reduced) index 524289 := by
  rintro ⟨flags, _, same⟩
  have bounded : (Blake2Round.controlAt flags index).Bounded := by
    have power := Nat.mod_lt (2 ^ index) (by decide : 0 < 1024)
    have flagBound := flags.isLt
    simp only [Blake2Round.controlAt, Word.Bounded, limbBase]
    omega
  have low : (Blake2Round.controlAt flags index).toBitVec.toNat % 65536 = 0 := by
    rw [Word.toBitVec_toNat bounded]
    simp [Blake2Round.controlAt, Word.value, limbBase]
  rw [← same] at low
  exact absurd low (by decide)

theorem special5_not_in_supported_registry {program : Program} (shapes : Shapes program)
    {entry : Delegation.Caller.ProgramEntry} (member : entry ∈ program.callers) :
    entry.data.family ≠ .keccak := by
  obtain ⟨bundle, _, _, _, family⟩ := shapes.coverage entry member
  rw [family]
  cases bundle.kind <;> simp [Kind.family]

theorem rom_pointer_rejected (kind : Kind) (left right : BitVec 32)
    (below : left.toNat < ROM.limit) : ¬ Pointers kind left right := by
  intro pointers
  exact Nat.not_le.mpr below pointers.1

theorem equal_g_pointers_rejected (reduced : Bool) (pointer : BitVec 32) :
    ¬ Pointers (.g reduced) pointer pointer := by
  intro pointers
  exact pointers.2.2.1 rfl

theorem interior_initial_entry_rejected [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    {program : Program} {initial : State}
    (member : (⟨4096, .g true⟩ : Bundle) ∈ program.bundles)
    (pc : AtPC initial 4100) :
    ControlAt (.g true) 0 128 ∧ ¬ ValidDelegationUse program initial := by
  refine ⟨rfl, ?_⟩
  intro valid
  exact valid.initialEntry ⟨4096, .g true⟩ member ⟨1, by decide⟩ (by decide) pc

/-- The contract admits programs without delegations without requiring any
native witness, successful final execution or algorithm result. -/
theorem empty_program_supported [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (ordinary : List Airbender.UnifiedReduced.ProgramEntry) (initial : State) :
    ValidDelegationUse ⟨ordinary, [], []⟩ initial := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor <;> simp
  · simp
  · simp
  · simp

end Tests.SupportedDelegationUse
