module
public import Human.Trace.UnifiedReduced.Proth120NativeTrace
public import Human.Helpers.Context.PaddingBoundary.Model

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120
open Trace PaddingBoundary Compiler.NativeMemory

/-- One side of the native PC and memory permutation, including the identity factor of each disabled port. -/
noncomputable def maskedTokens (trace : WrapTrace) (state : PCState.State proth120Modulus) (boundary : List (MemoryToken proth120Modulus))
    (pc : Row proth120Modulus Kind → PCState.State proth120Modulus) (ports : Row proth120Modulus Kind → List (MemoryToken proth120Modulus)) :=
  let maskRows := contributions trace.rows (fun row => row.assignment row.columns.execute)
  some (stateToken state) :: maskRows (fun r => [stateToken (pc r)]) ++ boundary.map some ++ maskRows ports

structure PaddedInputs (trace : WrapTrace) (initial : RV.State) (cells : List Cell) : Prop
    extends TraceBoundary (active trace) initial cells where
  permutation : (maskedTokens trace trace.initial trace.initialMemory Row.finish Row.writes).Perm
    (maskedTokens trace trace.terminal trace.terminalMemory Row.start Row.reads)
  rows : ∀ r ∈ trace.rows, (r.assignment r.columns.execute = 1 → r.start.word.toBitVec.toNat % 4 = 0 ∧ r.start.word.toBitVec.toNat + 4 ≤ romEnd) ∧
    NativeRowEvidence trace initial r

def PaddedTraceSoundnessClaim : Prop := ∀ trace initial cells, PaddedInputs trace initial cells → TraceResult (active trace) initial cells

def PaddedTraceSoundnessSatisfiableClaim : Prop := ∃ trace initial cells, PaddedInputs trace initial cells ∧
  trace.rows.length = 2 ∧ (active trace).rows.length = 1 ∧ (inactive trace).rows.length = 1

end Airbender.UnifiedReduced.Proth120
