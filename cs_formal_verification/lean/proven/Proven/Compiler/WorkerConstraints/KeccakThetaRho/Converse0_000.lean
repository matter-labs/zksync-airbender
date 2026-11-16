module
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Source
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Tuples
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Fields000
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Fields001
public import Proven.Compiler.WorkerConstraints.KeccakThetaRho.Fields002

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakThetaRho
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards1 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand1.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  apply (refinement1 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 1) (by change 1 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards2 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand2.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  apply (refinement2 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 2) (by change 2 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards3 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand3.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  apply (refinement3 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 3) (by change 3 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards4 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand4.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  apply (refinement4 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 4) (by change 4 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards5 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand5.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  apply (refinement5 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 5) (by change 5 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards6 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand6.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  apply (refinement6 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 6) (by change 6 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards7 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand7.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  apply (refinement7 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 7) (by change 7 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards8 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand8.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  apply (refinement8 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 8) (by change 8 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards9 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand9.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  apply (refinement9 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 9) (by change 9 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards10 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand10.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  apply (refinement10 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 10) (by change 10 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards11 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand11.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  apply (refinement11 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 11) (by change 11 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards12 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand12.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  apply (refinement12 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 12) (by change 12 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards13 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand13.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  apply (refinement13 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 13) (by change 13 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards14 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand14.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  apply (refinement14 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 14) (by change 14 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards15 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand15.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  apply (refinement15 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 15) (by change 15 < 53; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards16 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∃ index, operand16.input.fields physical = NativeWorkerSetup.rows .thetaRho 0 index := by
  apply (refinement16 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 16) (by change 16 < 53; decide)

/-- Each tuple in this native segment has an interpreted public row. -/
theorem converse0_000 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.KeccakThetaRho.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .thetaRho)) :
    ∀ values ∈ tuple0_000 physical, ∃ index, values = NativeWorkerSetup.rows .thetaRho 0 index :=
  (all_cons (backwards1 physical logical agreement holds) (all_cons (backwards2 physical logical agreement holds) (all_cons (backwards3 physical logical agreement holds) (all_cons (backwards4 physical logical agreement holds) (all_cons (backwards5 physical logical agreement holds) (all_cons (backwards6 physical logical agreement holds) (all_cons (backwards7 physical logical agreement holds) (all_cons (backwards8 physical logical agreement holds) (all_cons (backwards9 physical logical agreement holds) (all_cons (backwards10 physical logical agreement holds) (all_cons (backwards11 physical logical agreement holds) (all_cons (backwards12 physical logical agreement holds) (all_cons (backwards13 physical logical agreement holds) (all_cons (backwards14 physical logical agreement holds) (all_cons (backwards15 physical logical agreement holds) (all_cons (backwards16 physical logical agreement holds) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.KeccakThetaRho
