module
public import Human.ISA.ValidUse.Theorems
public import Proven.Final.ISA.DelegationRuns

@[expose] public section
namespace RV.ValidUse.Proofs
open Spec
set_option warningAsError true

/-- Valid bigint controls and RAM buffers select the reference arithmetic branch. -/
theorem bigint_reference : BigintReferenceClaim := by
  intro state valid
  obtain ⟨left, right, apart, control⟩ := valid
  have different : state.getReg 10 ≠ state.getReg 11 := by
    intro same
    rw [same] at apart
    rcases apart with one | two <;> omega
  have low : (state.getReg 12).toNat % 2 ^ 16 < 256 :=
    (Nat.mod_le _ _).trans_lt control.1
  simp only [Delegation.effect, Delegation.bigint, bigintReference, State.delegationRAM]
  rw [ite_eq_left ⟨left.2.1, right.2.2, right.2.1, different, low⟩]

/-- Both complete G schedules keep their independent BLAKE2s round reference. -/
theorem g_reference : GReferenceClaim := by
  intro reduced state left right valid
  cases reduced
  · exact blake_g_run10.1 state left right valid.2.2.2
  · exact blake_g_run.1 state left right valid.2.2.2

/-- Both round schedules compute the independent compression function. -/
theorem round_reference : RoundReferenceClaim := by
  intro reduced state left right counter last valid
  cases reduced
  · exact blake_compress_run10.1 state left right counter last valid.2.2
  · exact blake_compress_run.1 state left right counter last valid.2.2

/-- Compression mode computes the independent two-to-one hash in both schedules. -/
theorem hash_reference : HashReferenceClaim := by
  intro reduced right state left sibling valid
  cases reduced
  · exact blake_hash_run10.1 state left sibling right valid.2.2
  · cases right
    · exact blake_hash_run.1 state left sibling false valid.2.2
    · exact blake_hash_run.1 state left sibling true valid.2.2

/-- The complete valid split schedule computes Keccak-f[1600]. -/
theorem split_keccak_reference : SplitKeccakReferenceClaim := fun state pointer valid =>
  keccak_f1600_run.1 state pointer valid.2

/-- The complete valid special5 schedule computes Keccak-f[1600]. -/
theorem special5_reference : Special5ReferenceClaim := fun state pointer valid =>
  keccak_special5_run.1 state pointer valid.2

end RV.ValidUse.Proofs
