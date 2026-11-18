module
public import Proven.KernelExact
public import Proven.Compiler.WorkerBindings.KeccakChi5.Placement000
public import Proven.Compiler.WorkerBindings.KeccakChi5.Placement001
public import Proven.Compiler.WorkerBindings.KeccakChi5.Placement002
public import Proven.Compiler.WorkerBindings.KeccakChi5.Placement003
public import Proven.Compiler.WorkerBindings.KeccakChi5.Placement004
public import Proven.Compiler.WorkerBindings.KeccakChi5.Placement005
public import Proven.Compiler.WorkerBindings.KeccakChi5.Placement006
public import Proven.Compiler.WorkerBindings.KeccakChi5.Placement007
public import Proven.Compiler.WorkerBindings.KeccakChi5.Placement008
public import Proven.Compiler.WorkerBindings.KeccakChi5.Placement009
public import Proven.Compiler.WorkerBindings.KeccakChi5.Placement010
public import Proven.Compiler.WorkerBindings.KeccakChi5.Placement011
public import Proven.Compiler.WorkerBindings.KeccakChi5.Gates000
public import Proven.Compiler.WorkerBindings.KeccakChi5.Gates001
public import Proven.Compiler.WorkerBindings.KeccakChi5.Gates002

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerBindings.KeccakChi5
open Airbender Airbender.Compiler NativeArithmetic NativeBridge
set_option maxRecDepth 32768
/-- The checked typed relations supply every native scalar gate and cache. -/
theorem native_holds (physical : GKRAddress → F)
    (holds : Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.artifact.LoweredHolds (fun index => physical addresses[index])) :
    Holds Airbender.Compiler.Captures.KeccakChi5.imported.circuit physical := by
  apply native_of_base (by kernel_rfl)
  kernel_exact (append_zero (clauses000 physical holds) (append_zero (clauses001 physical holds) (append_zero (clauses002 physical holds) (show ∀ clause ∈ ([] : List Clause), clause.residual physical = 0 from by intro clause member; cases member))))

/-- The typed source equations are exactly the imported description equations. -/
theorem description :
    Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.artifact.source.map (fun expression => FlatOperation.assert (DescriptionBridge.toClean expression)) =
      Circuit.equations Airbender.Compiler.Captures.KeccakChi5.imported.circuit := by kernel_rfl

/-- Actual native gates and source placements imply every description equation. -/
theorem arithmetic : KeccakChi5CachedArithmeticClaim := by
  intro physical logical accepted agreement
  have gates : Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.artifact.LoweredHolds (fun index => physical addresses[index]) :=
    (append_holds (gates000 physical accepted) (append_holds (gates001 physical accepted) (append_holds (gates002 physical accepted) (by intro gate member; cases member))))
  have bindings : ∀ index ∈ List.range 189, placed physical logical index = logical index :=
    (append_placements (placements000 physical logical agreement) (append_placements (placements001 physical logical agreement) (append_placements (placements002 physical logical agreement) (append_placements (placements003 physical logical agreement) (append_placements (placements004 physical logical agreement) (append_placements (placements005 physical logical agreement) (append_placements (placements006 physical logical agreement) (append_placements (placements007 physical logical agreement) (append_placements (placements008 physical logical agreement) (append_placements (placements009 physical logical agreement) (append_placements (placements010 physical logical agreement) (append_placements (placements011 physical logical agreement) (by intro index member; cases member)))))))))))))
  have same : (fun index => physical addresses[Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.artifact.placement index]) =
      (fun index => logical index.val) := by
    funext index
    simpa only [placed, dite_eq_left index.isLt] using
      bindings index.val (List.mem_range.mpr index.isLt)
  have source := Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.artifact.backward Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.selected Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.extension
    Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.certificate Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.gatesChecked Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.checked gates
  change Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.artifact.SourceHolds
    (fun index => physical addresses[Airbender.Compiler.WorkerArithmetic.KeccakChi5.native.artifact.placement index]) at source
  rw [same] at source
  rw [← description]
  exact DescriptionBridge.assertions _ _ source
end Airbender.Compiler.WorkerBindings.KeccakChi5
