module
public import Proven.Compiler.WorkerArithmetic.KeccakThetaRho
public import Human.Compiler.Captures.KeccakThetaRho
public import Proven.Compiler.DescriptionBridge
public import Proven.Compiler.WorkerBindings.KeccakThetaRho.Data
public import Proven.Compiler.Reverse
public import Proven.KernelExact
public import Proven.KernelRfl

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerBindings.KeccakThetaRho
open Airbender Airbender.Compiler NativeArithmetic NativeBridge
set_option maxRecDepth 32768
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding8 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate8 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[51]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate8 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate8.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate8.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨8, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding8 physical).trans (gate_at accepted ⟨0, by decide⟩ ⟨51, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause8 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[51]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate8.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨8, by decide⟩)
  exact (binding8 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨8, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding9 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate9 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[52]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate9 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate9.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate9.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨9, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding9 physical).trans (gate_at accepted ⟨0, by decide⟩ ⟨52, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause9 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[52]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate9.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨9, by decide⟩)
  exact (binding9 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨9, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding10 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate10 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[53]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate10 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate10.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate10.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨10, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding10 physical).trans (gate_at accepted ⟨0, by decide⟩ ⟨53, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause10 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[53]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate10.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨10, by decide⟩)
  exact (binding10 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨10, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding11 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate11 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[54]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate11 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate11.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate11.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨11, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding11 physical).trans (gate_at accepted ⟨0, by decide⟩ ⟨54, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause11 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[54]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate11.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨11, by decide⟩)
  exact (binding11 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨11, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding12 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate12 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[55]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate12 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate12.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate12.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨12, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding12 physical).trans (gate_at accepted ⟨0, by decide⟩ ⟨55, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause12 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[55]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate12.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨12, by decide⟩)
  exact (binding12 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨12, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding13 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate13 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[56]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate13 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate13.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate13.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨13, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding13 physical).trans (gate_at accepted ⟨0, by decide⟩ ⟨56, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause13 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[56]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate13.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨13, by decide⟩)
  exact (binding13 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨13, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding14 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate14 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[57]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate14 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate14.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate14.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨14, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding14 physical).trans (gate_at accepted ⟨0, by decide⟩ ⟨57, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause14 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[57]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate14.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨14, by decide⟩)
  exact (binding14 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨14, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding15 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate15 (fun index => physical addresses[index]) =
      (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[58]'(by decide)).enforced_relation).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate15 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate15.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate15.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨15, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding15 physical).trans (gate_at accepted ⟨0, by decide⟩ ⟨58, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause15 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[58]'(by decide)).enforced_relation).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate15.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gatesChecked _ (List.get_mem _ ⟨15, by decide⟩)
  exact (binding15 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨15, by decide⟩)))
theorem gates001 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate8, Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate9, Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate10, Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate11, Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate12, Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate13, Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate14, Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.gate15], gate.expressionResidual (fun index => physical addresses[index]) = 0 :=
  (cons_holds (gate8 physical accepted) (cons_holds (gate9 physical accepted) (cons_holds (gate10 physical accepted) (cons_holds (gate11 physical accepted) (cons_holds (gate12 physical accepted) (cons_holds (gate13 physical accepted) (cons_holds (gate14 physical accepted) (cons_holds (gate15 physical accepted) (by intro gate member; cases member)))))))))

theorem clauses001 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakThetaRho.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    ∀ clause ∈ [(Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[51]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[52]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[53]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[54]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[55]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[56]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[57]'(by decide)).enforced_relation), (Clause.gate ((((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates ++ ((Airbender.Compiler.Captures.KeccakThetaRho.imported.circuit).layers[0]'(by decide)).gates_with_external_connections)[58]'(by decide)).enforced_relation)], clause.residual physical = 0 :=
  (cons_zero (clause8 physical holds) (cons_zero (clause9 physical holds) (cons_zero (clause10 physical holds) (cons_zero (clause11 physical holds) (cons_zero (clause12 physical holds) (cons_zero (clause13 physical holds) (cons_zero (clause14 physical holds) (cons_zero (clause15 physical holds) (by intro clause member; cases member)))))))))
end Airbender.Compiler.WorkerBindings.KeccakThetaRho
