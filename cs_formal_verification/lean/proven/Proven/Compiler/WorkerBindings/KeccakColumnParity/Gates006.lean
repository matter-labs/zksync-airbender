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
theorem binding48 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate48 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[61]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate48 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate48.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate48.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨48, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding48 physical).trans (gate_at accepted ⟨0, by decide⟩ ⟨61, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause48 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[61]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate48.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨48, by decide⟩)
  exact (binding48 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨48, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding49 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate49 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[62]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate49 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate49.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate49.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨49, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding49 physical).trans (gate_at accepted ⟨0, by decide⟩ ⟨62, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause49 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[62]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate49.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨49, by decide⟩)
  exact (binding49 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨49, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding50 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate50 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[63]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate50 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate50.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate50.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨50, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding50 physical).trans (gate_at accepted ⟨0, by decide⟩ ⟨63, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause50 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[63]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate50.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨50, by decide⟩)
  exact (binding50 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨50, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding51 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate51 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[64]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate51 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate51.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate51.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨51, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding51 physical).trans (gate_at accepted ⟨0, by decide⟩ ⟨64, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause51 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[64]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate51.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨51, by decide⟩)
  exact (binding51 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨51, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding52 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate52 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate52 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate52.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate52.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨52, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding52 physical).trans (gate_at accepted ⟨1, by decide⟩ ⟨0, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause52 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate52.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨52, by decide⟩)
  exact (binding52 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨52, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding53 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate53 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[2]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[2]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate53 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate53.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate53.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨53, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding53 physical).trans (gate_at accepted ⟨2, by decide⟩ ⟨0, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause53 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[2]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[2]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate53.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨53, by decide⟩)
  exact (binding53 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨53, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding54 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate54 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[3]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[3]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate54 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate54.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate54.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨54, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding54 physical).trans (gate_at accepted ⟨3, by decide⟩ ⟨0, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause54 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[3]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[3]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate54.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨54, by decide⟩)
  exact (binding54 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨54, by decide⟩)))
theorem gates006 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate48, Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate49, Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate50, Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate51, Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate52, Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate53, Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate54], gate.expressionResidual (fun index => physical addresses[index]) = 0 :=
  (cons_holds (gate48 physical accepted) (cons_holds (gate49 physical accepted) (cons_holds (gate50 physical accepted) (cons_holds (gate51 physical accepted) (cons_holds (gate52 physical accepted) (cons_holds (gate53 physical accepted) (cons_holds (gate54 physical accepted) (by intro gate member; cases member))))))))

theorem clauses006 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    ∀ clause ∈ [(Clause.gate ((((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[61]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[62]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[63]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[64]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[2]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[2]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[3]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[3]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation)], clause.residual physical = 0 :=
  (cons_zero (clause48 physical holds) (cons_zero (clause49 physical holds) (cons_zero (clause50 physical holds) (cons_zero (clause51 physical holds) (cons_zero (clause52 physical holds) (cons_zero (clause53 physical holds) (cons_zero (clause54 physical holds) (by intro clause member; cases member))))))))
end Airbender.Compiler.WorkerBindings.KeccakColumnParity
