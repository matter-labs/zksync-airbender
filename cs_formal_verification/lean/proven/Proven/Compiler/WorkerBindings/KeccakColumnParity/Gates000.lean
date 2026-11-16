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
theorem binding0 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate0 (fun index => physical addresses[index]) =
      (Clause.cache (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[30]'(by decide)).1 (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[30]'(by decide)).2).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate0 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate0.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate0.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨0, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding0 physical).trans (cache_at accepted ⟨0, by decide⟩ ⟨30, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause0 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.cache (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[30]'(by decide)).1 (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[30]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate0.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨0, by decide⟩)
  exact (binding0 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨0, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding1 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate1 (fun index => physical addresses[index]) =
      (Clause.cache (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[31]'(by decide)).1 (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[31]'(by decide)).2).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate1 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate1.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate1.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨1, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding1 physical).trans (cache_at accepted ⟨0, by decide⟩ ⟨31, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause1 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.cache (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[31]'(by decide)).1 (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[31]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate1.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨1, by decide⟩)
  exact (binding1 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨1, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding2 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate2 (fun index => physical addresses[index]) =
      (Clause.cache (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[32]'(by decide)).1 (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[32]'(by decide)).2).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate2 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate2.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate2.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨2, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding2 physical).trans (cache_at accepted ⟨0, by decide⟩ ⟨32, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause2 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.cache (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[32]'(by decide)).1 (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[32]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate2.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨2, by decide⟩)
  exact (binding2 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨2, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding3 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate3 (fun index => physical addresses[index]) =
      (Clause.cache (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[33]'(by decide)).1 (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[33]'(by decide)).2).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate3 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate3.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate3.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨3, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding3 physical).trans (cache_at accepted ⟨0, by decide⟩ ⟨33, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause3 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.cache (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[33]'(by decide)).1 (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[33]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate3.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨3, by decide⟩)
  exact (binding3 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨3, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding4 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate4 (fun index => physical addresses[index]) =
      (Clause.cache (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[34]'(by decide)).1 (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[34]'(by decide)).2).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate4 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate4.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate4.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨4, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding4 physical).trans (cache_at accepted ⟨0, by decide⟩ ⟨34, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause4 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.cache (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[34]'(by decide)).1 (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[34]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate4.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨4, by decide⟩)
  exact (binding4 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨4, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding5 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate5 (fun index => physical addresses[index]) =
      (Clause.cache (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[35]'(by decide)).1 (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[35]'(by decide)).2).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate5 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate5.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate5.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨5, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding5 physical).trans (cache_at accepted ⟨0, by decide⟩ ⟨35, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause5 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.cache (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[35]'(by decide)).1 (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[35]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate5.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨5, by decide⟩)
  exact (binding5 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨5, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding6 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate6 (fun index => physical addresses[index]) =
      (Clause.cache (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[36]'(by decide)).1 (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[36]'(by decide)).2).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate6 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate6.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate6.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨6, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding6 physical).trans (cache_at accepted ⟨0, by decide⟩ ⟨36, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause6 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.cache (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[36]'(by decide)).1 (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[36]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate6.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨6, by decide⟩)
  exact (binding6 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨6, by decide⟩)))
/-- This typed sparse residual is the actual physical native relation. -/
theorem binding7 (physical : GKRAddress → F) :
    sparseResidual Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate7 (fun index => physical addresses[index]) =
      (Clause.cache (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[37]'(by decide)).1 (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[37]'(by decide)).2).residual physical := by kernel_rfl

/-- The physical native relation supplies the checked typed residual. -/
theorem gate7 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical) :
    Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate7.expressionResidual (fun index => physical addresses[index]) = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate7.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨7, by decide⟩)
  exact (sparse_checked checked _).symm.trans
    ((binding7 physical).trans (cache_at accepted ⟨0, by decide⟩ ⟨37, by decide⟩))

/-- The checked typed residual supplies the physical native relation. -/
theorem clause7 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    (Clause.cache (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[37]'(by decide)).1 (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[37]'(by decide)).2).residual physical = 0 := by
  have checked : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate7.check = true :=
    List.all_eq_true.mp Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked _ (List.get_mem _ ⟨7, by decide⟩)
  exact (binding7 physical).symm.trans
    ((sparse_checked checked _).trans (holds _ (List.get_mem _ ⟨7, by decide⟩)))
theorem gates000 (physical : GKRAddress → F) (accepted : Holds Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical) :
    ∀ gate ∈ [Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate0, Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate1, Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate2, Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate3, Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate4, Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate5, Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate6, Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gate7], gate.expressionResidual (fun index => physical addresses[index]) = 0 :=
  (cons_holds (gate0 physical accepted) (cons_holds (gate1 physical accepted) (cons_holds (gate2 physical accepted) (cons_holds (gate3 physical accepted) (cons_holds (gate4 physical accepted) (cons_holds (gate5 physical accepted) (cons_holds (gate6 physical accepted) (cons_holds (gate7 physical accepted) (by intro gate member; cases member)))))))))

theorem clauses000 (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    ∀ clause ∈ [(Clause.cache (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[30]'(by decide)).1 (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[30]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[31]'(by decide)).1 (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[31]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[32]'(by decide)).1 (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[32]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[33]'(by decide)).1 (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[33]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[34]'(by decide)).1 (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[34]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[35]'(by decide)).1 (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[35]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[36]'(by decide)).1 (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[36]'(by decide)).2), (Clause.cache (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[37]'(by decide)).1 (((Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit).layers[0]'(by decide)).cached_relations[37]'(by decide)).2)], clause.residual physical = 0 :=
  (cons_zero (clause0 physical holds) (cons_zero (clause1 physical holds) (cons_zero (clause2 physical holds) (cons_zero (clause3 physical holds) (cons_zero (clause4 physical holds) (cons_zero (clause5 physical holds) (cons_zero (clause6 physical holds) (cons_zero (clause7 physical holds) (by intro clause member; cases member)))))))))
end Airbender.Compiler.WorkerBindings.KeccakColumnParity
