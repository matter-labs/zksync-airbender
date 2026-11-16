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
theorem binding8 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate8 (fun index => physical addresses[index]) =
      (Clause.cache (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[38]'(by decide)).1 (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[38]'(by decide)).2).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate8 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate8.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate8.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨8, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding8 physical).trans (cache_at accepted ⟨0, by decide⟩ ⟨38, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause8 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.cache (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[38]'(by decide)).1 (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[38]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate8.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨8, by decide⟩)
  exact (binding8 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨8, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding9 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate9 (fun index => physical addresses[index]) =
      (Clause.cache (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[39]'(by decide)).1 (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[39]'(by decide)).2).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate9 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate9.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate9.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨9, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding9 physical).trans (cache_at accepted ⟨0, by decide⟩ ⟨39, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause9 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.cache (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[39]'(by decide)).1 (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[39]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate9.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨9, by decide⟩)
  exact (binding9 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨9, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding10 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate10 (fun index => physical addresses[index]) =
      (Clause.cache (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[40]'(by decide)).1 (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[40]'(by decide)).2).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate10 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate10.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate10.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨10, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding10 physical).trans (cache_at accepted ⟨0, by decide⟩ ⟨40, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause10 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.cache (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[40]'(by decide)).1 (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[40]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate10.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨10, by decide⟩)
  exact (binding10 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨10, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding11 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate11 (fun index => physical addresses[index]) =
      (Clause.cache (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[41]'(by decide)).1 (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[41]'(by decide)).2).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate11 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate11.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate11.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨11, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding11 physical).trans (cache_at accepted ⟨0, by decide⟩ ⟨41, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause11 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.cache (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[41]'(by decide)).1 (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[41]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate11.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨11, by decide⟩)
  exact (binding11 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨11, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding12 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate12 (fun index => physical addresses[index]) =
      (Clause.cache (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[42]'(by decide)).1 (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[42]'(by decide)).2).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate12 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate12.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate12.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨12, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding12 physical).trans (cache_at accepted ⟨0, by decide⟩ ⟨42, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause12 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.cache (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[42]'(by decide)).1 (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[42]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate12.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨12, by decide⟩)
  exact (binding12 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨12, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding13 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate13 (fun index => physical addresses[index]) =
      (Clause.cache (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[43]'(by decide)).1 (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[43]'(by decide)).2).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate13 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate13.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate13.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨13, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding13 physical).trans (cache_at accepted ⟨0, by decide⟩ ⟨43, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause13 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.cache (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[43]'(by decide)).1 (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[43]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate13.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨13, by decide⟩)
  exact (binding13 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨13, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding14 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate14 (fun index => physical addresses[index]) =
      (Clause.cache (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[44]'(by decide)).1 (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[44]'(by decide)).2).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate14 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate14.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate14.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨14, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding14 physical).trans (cache_at accepted ⟨0, by decide⟩ ⟨44, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause14 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.cache (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[44]'(by decide)).1 (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[44]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate14.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨14, by decide⟩)
  exact (binding14 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨14, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding15 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate15 (fun index => physical addresses[index]) =
      (Clause.cache (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[45]'(by decide)).1 (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[45]'(by decide)).2).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate15 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate15.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate15.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨15, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding15 physical).trans (cache_at accepted ⟨0, by decide⟩ ⟨45, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause15 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.cache (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[45]'(by decide)).1 (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[45]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate15.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨15, by decide⟩)
  exact (binding15 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨15, by decide⟩)))
theorem gates001 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate8, Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate9, Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate10, Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate11, Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate12, Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate13, Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate14, Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate15], gate.expressionResidual (fun index => physical addresses[index]) = 0 :=
  (cons_holds (gate8 physical accepted) (cons_holds (gate9 physical accepted) (cons_holds (gate10 physical accepted) (cons_holds (gate11 physical accepted) (cons_holds (gate12 physical accepted) (cons_holds (gate13 physical accepted) (cons_holds (gate14 physical accepted) (cons_holds (gate15 physical accepted) (by intro gate member; cases member)))))))))

theorem clauses001 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    ∀ clause ∈ [(Clause.cache (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[38]'(by decide)).1 (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[38]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[39]'(by decide)).1 (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[39]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[40]'(by decide)).1 (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[40]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[41]'(by decide)).1 (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[41]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[42]'(by decide)).1 (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[42]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[43]'(by decide)).1 (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[43]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[44]'(by decide)).1 (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[44]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[45]'(by decide)).1 (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[45]'(by decide)).2)], clause.residual physical = 0 :=
  (cons_zero (clause8 physical holds) (cons_zero (clause9 physical holds) (cons_zero (clause10 physical holds) (cons_zero (clause11 physical holds) (cons_zero (clause12 physical holds) (cons_zero (clause13 physical holds) (cons_zero (clause14 physical holds) (cons_zero (clause15 physical holds) (by intro clause member; cases member)))))))))
end Airbender.Compiler.WorkerBindings.KeccakColumnParity
