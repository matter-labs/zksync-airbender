import Airbender.Proofs.GKRProtocol.MemoryTokens

namespace Tests.GKRMemoryTokens
open Airbender Airbender.Compiler
set_option warningAsError true

def first : Trace.MemoryToken babyBearModulus :=
  ⟨Nat.pair 0 (Nat.pair 1 0), (0, 0), Nat.pair 70000 0⟩

def second : Trace.MemoryToken babyBearModulus :=
  ⟨Nat.pair 0 (Nat.pair 2 0), (0, 0), Nat.pair 70000 0⟩

theorem distinct_logical_tokens : first ≠ second := by decide +kernel

/-- One sampled algebraic equality supplies no exact token matching. -/
theorem distinct_tokens_can_have_equal_sampled_fingerprints :
    memoryTokenFingerprint (RingHom.id Source.BaseField) ⟨0, 0, fun _ => 0⟩ first =
      memoryTokenFingerprint (RingHom.id Source.BaseField) ⟨0, 0, fun _ => 0⟩ second := by
  simp [memoryTokenFingerprint, first, second]

theorem raw_data_limb_is_not_truncated : (Nat.unpair first.value).1 = 70000 := by
  simp [first]

theorem pc_state_uses_separate_address_space (state : PCState.State babyBearModulus) :
    (Nat.unpair (pcStateMemoryToken state).address).1 = 2 := by
  simp [pcStateMemoryToken]

end Tests.GKRMemoryTokens
