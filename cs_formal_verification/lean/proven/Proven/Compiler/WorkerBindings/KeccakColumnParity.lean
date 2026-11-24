module
public import Proven.KernelExact
public import Proven.Compiler.WorkerBindings.KeccakColumnParity.Placement000
public import Proven.Compiler.WorkerBindings.KeccakColumnParity.Placement001
public import Proven.Compiler.WorkerBindings.KeccakColumnParity.Placement002
public import Proven.Compiler.WorkerBindings.KeccakColumnParity.Placement003
public import Proven.Compiler.WorkerBindings.KeccakColumnParity.Placement004
public import Proven.Compiler.WorkerBindings.KeccakColumnParity.Placement005
public import Proven.Compiler.WorkerBindings.KeccakColumnParity.Placement006
public import Proven.Compiler.WorkerBindings.KeccakColumnParity.Placement007
public import Proven.Compiler.WorkerBindings.KeccakColumnParity.Placement008
public import Proven.Compiler.WorkerBindings.KeccakColumnParity.Placement009
public import Proven.Compiler.WorkerBindings.KeccakColumnParity.Placement010
public import Proven.Compiler.WorkerBindings.KeccakColumnParity.Gates000
public import Proven.Compiler.WorkerBindings.KeccakColumnParity.Gates001
public import Proven.Compiler.WorkerBindings.KeccakColumnParity.Gates002
public import Proven.Compiler.WorkerBindings.KeccakColumnParity.Gates003
public import Proven.Compiler.WorkerBindings.KeccakColumnParity.Gates004
public import Proven.Compiler.WorkerBindings.KeccakColumnParity.Gates005
public import Proven.Compiler.WorkerBindings.KeccakColumnParity.Gates006

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerBindings.KeccakColumnParity
open Airbender Airbender.Compiler NativeArithmetic NativeBridge
set_option maxRecDepth 32768
/-- The checked typed relations supply every native scalar gate and cache. -/
theorem native_holds (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    Holds Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit physical := by
  apply native_of_base (by kernel_rfl)
  kernel_exact (append_zero (clauses000 physical holds) (append_zero (clauses001 physical holds) (append_zero (clauses002 physical holds) (append_zero (clauses003 physical holds) (append_zero (clauses004 physical holds) (append_zero (clauses005 physical holds) (append_zero (clauses006 physical holds) (show ∀ clause ∈ ([] : List Clause), clause.residual physical = 0 from by intro clause member; cases member))))))))

/-- The typed source equations are exactly the imported description equations. -/
theorem description :
    Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.artifact.source.map (fun expression => FlatOperation.assert (DescriptionBridge.toClean expression)) =
      Circuit.equations Airbender.Compiler.Captures.KeccakColumnParity.imported.circuit := by kernel_rfl

/-- Actual native gates and source placements imply every description equation. -/
theorem arithmetic : KeccakColumnParityCachedArithmeticClaim := by
  intro physical logical accepted agreement
  have gates : Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.artifact.LoweredHolds (fun index => physical addresses[index]) :=
    (append_holds (gates000 physical accepted) (append_holds (gates001 physical accepted) (append_holds (gates002 physical accepted) (append_holds (gates003 physical accepted) (append_holds (gates004 physical accepted) (append_holds (gates005 physical accepted) (append_holds (gates006 physical accepted) (by intro gate member; cases member))))))))
  have bindings : ∀ index ∈ List.range 167, placed physical logical index = logical index :=
    (append_placements (placements000 physical logical agreement) (append_placements (placements001 physical logical agreement) (append_placements (placements002 physical logical agreement) (append_placements (placements003 physical logical agreement) (append_placements (placements004 physical logical agreement) (append_placements (placements005 physical logical agreement) (append_placements (placements006 physical logical agreement) (append_placements (placements007 physical logical agreement) (append_placements (placements008 physical logical agreement) (append_placements (placements009 physical logical agreement) (append_placements (placements010 physical logical agreement) (by intro index member; cases member))))))))))))
  have same : (fun index => physical addresses[Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.artifact.placement index]) =
      (fun index => logical index.val) := by
    funext index
    simpa only [placed, dite_eq_left index.isLt] using
      bindings index.val (List.mem_range.mpr index.isLt)
  have source := Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.artifact.backward Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.selected Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.extension
    Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.certificate Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.gatesChecked Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.checked gates
  change Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.artifact.SourceHolds
    (fun index => physical addresses[Airbender.Compiler.WorkerArithmetic.KeccakColumnParity.native.artifact.placement index]) at source
  rw [same] at source
  rw [← description]
  exact DescriptionBridge.assertions _ _ source
end Airbender.Compiler.WorkerBindings.KeccakColumnParity
