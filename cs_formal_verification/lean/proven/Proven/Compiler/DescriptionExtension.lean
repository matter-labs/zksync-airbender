module
public import Proven.Compiler.DescriptionBridge
public import Proven.GKRProtocol.BaseAssignment

@[expose] public section
namespace Airbender.Compiler.DescriptionBridge
open NativeArithmetic
set_option warningAsError true

/-- Reviewed flat assertions supply their typed source equations. -/
theorem source_of_assertions (source : List (Compiler.Expression n F)) (logical : Nat → F)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical)
      (source.map (fun expression => FlatOperation.assert (toClean expression)))) :
    ∀ expression ∈ source, expression.value (fun index => logical index.val) = 0 := by
  induction source with
  | nil => intro expression member; cases member
  | cons head tail ih =>
      intro expression member
      rcases List.mem_cons.mp member with rfl | member
      · exact (value _ logical).symm.trans holds.1
      · exact ih holds.2 expression member

/-- A complete checked arithmetic extension supplies every native scalar equation and preserves source placements. -/
theorem extension (circuit : Circuit) (artifact : ArithmeticArtifact n m F)
    (selected : List (Fin artifact.gates.length)) (extend : Fin m → Polynomial n F)
    (certificate : Certificate (artifact.translation selected extend))
    (gateChecks : artifact.gates.all ArithmeticGate.check = true)
    (checked : check (artifact.translation selected extend) certificate = true)
    (complete : selected = List.finRange artifact.gates.length)
    (bank : WireBank m)
    (roundTrip : ∀ index, bank.placement (bank.address index) = index)
    (placements : ∀ entry ∈ circuit.placement_data.entries,
      ∃ index : Fin n, index.val = entry.1 ∧ bank.address (artifact.placement index) = entry.2)
    (native : ∀ physical, artifact.LoweredHolds (physical ∘ bank.address) → Holds circuit physical)
    (logical : Nat → F)
    (source : artifact.SourceHolds (fun index => logical index.val)) :
    ∃ physical : GKRAddress → F, Holds circuit physical ∧ PlacementAgreement circuit physical logical := by
  obtain ⟨extended, preserved, gates⟩ := artifact.forward selected extend certificate gateChecks checked source
  have allGates : artifact.LoweredHolds extended := by
    intro gate member
    obtain ⟨index, rfl⟩ := List.mem_iff_get.mp member
    exact gates index (by rw [complete]; exact List.mem_finRange index)
  let physical := bank.materialize extended (fun _ => 0)
  refine ⟨physical, native physical (WireBank.materialize_gates bank roundTrip extended
    (fun _ => 0) artifact.gates allGates), ?_⟩
  intro entry member
  obtain ⟨index, same, location⟩ := placements entry member
  rw [← same, ← location]
  exact ((WireBank.materialize_at bank roundTrip extended (fun _ => 0)
    (artifact.placement index)).trans (preserved index)).symm

end Airbender.Compiler.DescriptionBridge
