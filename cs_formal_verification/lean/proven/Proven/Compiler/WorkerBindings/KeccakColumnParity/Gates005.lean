module
public import Proven.Compiler.WorkerArithmetic.KeccakColumnParity
public import Human.Compiler.Captures.KeccakColumnParity
public import Proven.Compiler.DescriptionBridge
public import Proven.Compiler.WorkerBindings.KeccakColumnParity.Data
public import Proven.Compiler.Reverse
public import Proven.KernelExact
public import Proven.KernelRfl

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerBindings.KeccakColumnParity
open Airbender Airbender.Compiler NativeArithmetic NativeBridge
set_option maxRecDepth 32768
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding40 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate40 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[53]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate40 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate40.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate40.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨40, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding40 physical).trans (gate_at accepted ⟨0, by decide⟩ ⟨53, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause40 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[53]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate40.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨40, by decide⟩)
  exact (binding40 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨40, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding41 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate41 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[54]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate41 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate41.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate41.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨41, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding41 physical).trans (gate_at accepted ⟨0, by decide⟩ ⟨54, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause41 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[54]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate41.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨41, by decide⟩)
  exact (binding41 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨41, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding42 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate42 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[55]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate42 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate42.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate42.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨42, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding42 physical).trans (gate_at accepted ⟨0, by decide⟩ ⟨55, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause42 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[55]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate42.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨42, by decide⟩)
  exact (binding42 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨42, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding43 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate43 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[56]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate43 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate43.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate43.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨43, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding43 physical).trans (gate_at accepted ⟨0, by decide⟩ ⟨56, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause43 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[56]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate43.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨43, by decide⟩)
  exact (binding43 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨43, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding44 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate44 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[57]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate44 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate44.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate44.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨44, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding44 physical).trans (gate_at accepted ⟨0, by decide⟩ ⟨57, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause44 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[57]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate44.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨44, by decide⟩)
  exact (binding44 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨44, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding45 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate45 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[58]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate45 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate45.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate45.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨45, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding45 physical).trans (gate_at accepted ⟨0, by decide⟩ ⟨58, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause45 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[58]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate45.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨45, by decide⟩)
  exact (binding45 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨45, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding46 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate46 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[59]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate46 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate46.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate46.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨46, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding46 physical).trans (gate_at accepted ⟨0, by decide⟩ ⟨59, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause46 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[59]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate46.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨46, by decide⟩)
  exact (binding46 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨46, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding47 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate47 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[60]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate47 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate47.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate47.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨47, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding47 physical).trans (gate_at accepted ⟨0, by decide⟩ ⟨60, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause47 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[60]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate47.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨47, by decide⟩)
  exact (binding47 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨47, by decide⟩)))
theorem gates005 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate40, Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate41, Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate42, Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate43, Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate44, Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate45, Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate46, Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate47], gate.expressionResidual (fun index => physical addresses[index]) = 0 :=
  (cons_holds (gate40 physical accepted) (cons_holds (gate41 physical accepted) (cons_holds (gate42 physical accepted) (cons_holds (gate43 physical accepted) (cons_holds (gate44 physical accepted) (cons_holds (gate45 physical accepted) (cons_holds (gate46 physical accepted) (cons_holds (gate47 physical accepted) (by intro gate member; cases member)))))))))

theorem clauses005 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    ∀ clause ∈ [(Clause.gate ((((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[53]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[54]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[55]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[56]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[57]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[58]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[59]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[60]'(by decide)).enforced_relation)], clause.residual physical = 0 :=
  (cons_zero (clause40 physical holds) (cons_zero (clause41 physical holds) (cons_zero (clause42 physical holds) (cons_zero (clause43 physical holds) (cons_zero (clause44 physical holds) (cons_zero (clause45 physical holds) (cons_zero (clause46 physical holds) (cons_zero (clause47 physical holds) (by intro clause member; cases member)))))))))
end Airbender.Compiler.WorkerBindings.KeccakColumnParity
