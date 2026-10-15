import Airbender.Review.Trace.ExternalBoundaries

namespace Tests.ExternalBoundaries
open Airbender Airbender.Trace Airbender.ExternalBoundary
set_option warningAsError true
set_option maxRecDepth 16384

private abbrev geometry : Initialization.Geometry := ⟨2 ^ 22, 256, by decide, by decide⟩
private def sparse : Initialization.Selection geometry := ⟨[254, 255], by decide⟩
private def reversed : Initialization.Selection geometry := ⟨[255, 254], by decide⟩

theorem sparse_window_domain :
    ((Initialization.cells sparse).map Cell.addressCode).Nodup ∧
    ((Initialization.cells reversed).map Cell.addressCode).Nodup :=
  ⟨(initialization_soundness sparse).1, (initialization_soundness reversed).1⟩

theorem duplicate_windows_excluded :
    ¬ ([254, 254] : List (Fin geometry.slots)).Nodup := by decide

theorem last_word_preserved :
    Initialization.address (geometry := geometry) (255, 4194303) = 4294967292 ∧
    Initialization.cell (geometry := geometry) (255, 4194303) = .ram 4294967292 := by decide

theorem out_of_range_window_excluded : ¬ ∃ index : Fin geometry.slots, index.val = 256 := by
  rintro ⟨index, equal⟩
  have := index.isLt
  change index.val < 256 at this
  omega

theorem zero_filler_is_not_unqueryable {trace : PooledTrace babyBearModulus} :
    ¬ Decoder.Binding trace [] (fun _ => [Vector.replicate 9 0]) 0 := by
  intro binding
  rcases binding.contents .addSub (Vector.replicate 9 0) (by simp) with real | filler
  · obtain ⟨_, absent, _⟩ := real
    simp at absent
  · norm_num at filler

theorem worker_ledger_counts_occurrences :
    ¬ ([((0, 0), 32)] : List ((Nat × Nat) × Nat)).Perm
      [((0, 0), 32), ((0, 0), 32)] := by
  intro equal
  have := equal.length_eq
  simp at this

theorem native_matching_does_not_supply_ledger :
    ∃ calls fulfillments : List (Delegation.Requests.Request babyBearModulus),
      Delegation.Requests.Matching calls fulfillments ∧ ¬ calls.Perm fulfillments := by
  refine ⟨[], [⟨Delegation.Requests.csr .blakeG, (0, 0)⟩], ?_, ?_⟩
  · exact List.Perm.refl _
  · intro equal
    have := equal.length_eq
    simp at this

theorem carry_and_copy_positions :
    (BigintABI.Command.word ⟨6, false⟩).lo = 128 ∧
    (BigintABI.Command.word ⟨6, true⟩).lo = 192 ∧
    (BigintABI.Command.word ⟨0, true⟩).lo = 65 := by decide

end Tests.ExternalBoundaries
