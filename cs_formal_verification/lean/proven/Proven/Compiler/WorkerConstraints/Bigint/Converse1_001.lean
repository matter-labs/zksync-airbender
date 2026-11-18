module
public import Proven.Compiler.WorkerConstraints.Bigint.Source
public import Proven.Compiler.WorkerConstraints.Bigint.Tuples
public import Proven.Compiler.WorkerConstraints.Bigint.Fields014
public import Proven.Compiler.WorkerConstraints.Bigint.Fields015
public import Proven.Compiler.WorkerConstraints.Bigint.Fields016

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.Bigint
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards118 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand118.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  apply (refinement118 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 17) (by change 17 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards119 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand119.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  apply (refinement119 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 18) (by change 18 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards120 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand120.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  apply (refinement120 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 19) (by change 19 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards121 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand121.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  apply (refinement121 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 20) (by change 20 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards122 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand122.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  apply (refinement122 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 21) (by change 21 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards123 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand123.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  apply (refinement123 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 22) (by change 22 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards124 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand124.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  apply (refinement124 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 23) (by change 23 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards125 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand125.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  apply (refinement125 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 24) (by change 24 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards126 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand126.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  apply (refinement126 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 25) (by change 25 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards127 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand127.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  apply (refinement127 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 26) (by change 26 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards128 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand128.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  apply (refinement128 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 27) (by change 27 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards129 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand129.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  apply (refinement129 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 28) (by change 28 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards130 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand130.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  apply (refinement130 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 29) (by change 29 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards131 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand131.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  apply (refinement131 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 30) (by change 30 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards132 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand132.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  apply (refinement132 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 31) (by change 31 < 136; decide)

/-- Accepted description lookups supply the native tuple at its actual placement. -/
theorem backwards133 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∃ index, operand133.input.fields physical = NativeWorkerSetup.rows .bigint 1 index := by
  apply (refinement133 physical logical agreement).mp
  apply (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp holds).2
  rw [source_binding]
  exact List.getElem_mem (l := sourceQueries) (n := 15) (by change 15 < 136; decide)

/-- Each tuple in this native segment has an interpreted public row. -/
theorem converse1_001 (physical : GKRAddress → F) (logical : Nat → F)
    (agreement : PlacementAgreement (Captures.Bigint.imported.circuit) physical logical)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment logical) (constraints .bigint)) :
    ∀ values ∈ tuple1_001 physical, ∃ index, values = NativeWorkerSetup.rows .bigint 1 index :=
  (all_cons (backwards118 physical logical agreement holds) (all_cons (backwards119 physical logical agreement holds) (all_cons (backwards120 physical logical agreement holds) (all_cons (backwards121 physical logical agreement holds) (all_cons (backwards122 physical logical agreement holds) (all_cons (backwards123 physical logical agreement holds) (all_cons (backwards124 physical logical agreement holds) (all_cons (backwards125 physical logical agreement holds) (all_cons (backwards126 physical logical agreement holds) (all_cons (backwards127 physical logical agreement holds) (all_cons (backwards128 physical logical agreement holds) (all_cons (backwards129 physical logical agreement holds) (all_cons (backwards130 physical logical agreement holds) (all_cons (backwards131 physical logical agreement holds) (all_cons (backwards132 physical logical agreement holds) (all_cons (backwards133 physical logical agreement holds) (by intro value member; cases member)))))))))))))))))

end Airbender.Compiler.WorkerConstraints.Bigint
