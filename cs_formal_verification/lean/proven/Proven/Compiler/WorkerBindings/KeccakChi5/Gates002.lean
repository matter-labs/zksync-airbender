module
public import Proven.Compiler.WorkerArithmetic.KeccakChi5
public import Human.Compiler.Captures.KeccakChi5
public import Proven.Compiler.DescriptionBridge
public import Proven.Compiler.WorkerBindings.KeccakChi5.Data
public import Proven.Compiler.Reverse
public import Proven.KernelExact
public import Proven.KernelRfl

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerBindings.KeccakChi5
open Airbender Airbender.Compiler NativeArithmetic NativeBridge
set_option maxRecDepth 32768
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding16 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.gate16 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakChi5.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakChi5.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[38]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate16 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.gate16.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.gate16.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.gatesChecked _ (List.get_mem _ ⟨16, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding16 physical).trans (gate_at accepted ⟨0, by decide⟩ ⟨38, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause16 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakChi5.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakChi5.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[38]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.gate16.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.gatesChecked _ (List.get_mem _ ⟨16, by decide⟩)
  exact (binding16 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨16, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding17 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.gate17 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakChi5.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakChi5.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[39]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate17 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.gate17.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.gate17.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.gatesChecked _ (List.get_mem _ ⟨17, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding17 physical).trans (gate_at accepted ⟨0, by decide⟩ ⟨39, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause17 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakChi5.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakChi5.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[39]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.gate17.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.gatesChecked _ (List.get_mem _ ⟨17, by decide⟩)
  exact (binding17 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨17, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding18 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.gate18 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakChi5.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakChi5.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[40]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate18 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.gate18.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.gate18.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.gatesChecked _ (List.get_mem _ ⟨18, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding18 physical).trans (gate_at accepted ⟨0, by decide⟩ ⟨40, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause18 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakChi5.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakChi5.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[40]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.gate18.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.gatesChecked _ (List.get_mem _ ⟨18, by decide⟩)
  exact (binding18 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨18, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding19 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.gate19 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakChi5.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakChi5.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate19 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.gate19.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.gate19.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.gatesChecked _ (List.get_mem _ ⟨19, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding19 physical).trans (gate_at accepted ⟨1, by decide⟩ ⟨0, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause19 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakChi5.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakChi5.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.gate19.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.gatesChecked _ (List.get_mem _ ⟨19, by decide⟩)
  exact (binding19 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨19, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding20 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.gate20 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakChi5.imported.circuit).layers[2]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakChi5.imported.circuit).layers[2]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate20 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.gate20.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.gate20.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.gatesChecked _ (List.get_mem _ ⟨20, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding20 physical).trans (gate_at accepted ⟨2, by decide⟩ ⟨0, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause20 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakChi5.imported.circuit).layers[2]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakChi5.imported.circuit).layers[2]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.gate20.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.gatesChecked _ (List.get_mem _ ⟨20, by decide⟩)
  exact (binding20 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨20, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding21 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.gate21 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakChi5.imported.circuit).layers[3]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakChi5.imported.circuit).layers[3]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate21 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.gate21.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.gate21.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.gatesChecked _ (List.get_mem _ ⟨21, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding21 physical).trans (gate_at accepted ⟨3, by decide⟩ ⟨0, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause21 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakChi5.imported.circuit).layers[3]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakChi5.imported.circuit).layers[3]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.gate21.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.gatesChecked _ (List.get_mem _ ⟨21, by decide⟩)
  exact (binding21 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨21, by decide⟩)))
theorem gates002 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.gate16, Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.gate17, Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.gate18, Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.gate19, Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.gate20, Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.gate21], gate.expressionResidual (fun index => physical addresses[index]) = 0 :=
  (cons_holds (gate16 physical accepted) (cons_holds (gate17 physical accepted) (cons_holds (gate18 physical accepted) (cons_holds (gate19 physical accepted) (cons_holds (gate20 physical accepted) (cons_holds (gate21 physical accepted) (by intro gate member; cases member)))))))

theorem clauses002 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    ∀ clause ∈ [(Clause.gate ((((Airbender.Compiler.Captures.KeccakChi5.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakChi5.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[38]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.KeccakChi5.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakChi5.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[39]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.KeccakChi5.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakChi5.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[40]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.KeccakChi5.imported.circuit).layers[1]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakChi5.imported.circuit).layers[1]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.KeccakChi5.imported.circuit).layers[2]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakChi5.imported.circuit).layers[2]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.KeccakChi5.imported.circuit).layers[3]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakChi5.imported.circuit).layers[3]'(by decide)).gates_with_external_connections)[0]'(by decide)).enforced_relation)], clause.residual physical = 0 :=
  (cons_zero (clause16 physical holds) (cons_zero (clause17 physical holds) (cons_zero (clause18 physical holds) (cons_zero (clause19 physical holds) (cons_zero (clause20 physical holds) (cons_zero (clause21 physical holds) (by intro clause member; cases member)))))))
end Airbender.Compiler.WorkerBindings.KeccakChi5
