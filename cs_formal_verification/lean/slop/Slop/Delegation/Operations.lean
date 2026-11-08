module
public import Human.Helpers.Delegation.Operations
public import Slop.Bigint.Memory
public import Slop.Blake2G.Memory
public import Slop.Blake2Round.Memory
public import Slop.Keccak.Memory

@[expose] public section

namespace Airbender.Delegation.Proofs
open Trace
set_option warningAsError true

theorem operation_rules_of_queries [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : MemoryData p} {control : Fin 4096 → Vector Nat 6}
    (constraints : ∀ row ∈ data.rows,
      FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (row.constraints data.setup))
    (tables : data.setup = modeledSetup control)
    (rounds : ∀ row ∈ data.rows, row.family = .blakeRound →
      ∃ round, Blake2Round.Memory.RoundMask row.assignment round)
    (keccakActive : ∀ row ∈ data.rows, row.family = .keccak → row.assignment Keccak.Variables.execute = 1) :
    WriteBoundsFromReads data := by
  intro row member reads
  cases row with
  | mk family w =>
    have h := constraints ⟨family, w⟩ member
    cases family
    all_goals simp only [Row.constraints, tables, modeledSetup] at h
    · exact Bigint.Proofs.memory_write_rule (by omega) h reads
    · -- the serialized inverse fixes p = BabyBear, above Blake2G's 2^25 bound
      have field : p = babyBearModulus :=
        Blake2Round.Proofs.scale128_field (by linear_combination inverse)
      exact Blake2G.Proofs.memory_write_rule (by rw [field]; unfold babyBearModulus; norm_num)
        inverse h reads
    · obtain ⟨round, mask⟩ := rounds ⟨.blakeRound, w⟩ member rfl
      exact Blake2Round.Proofs.memory_write_rule hp inverse h round mask reads
    · exact Keccak.Proofs.memory_write_rule (by omega) h
        (keccakActive ⟨.keccak, w⟩ member rfl) reads

end Airbender.Delegation.Proofs
