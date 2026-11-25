module
public import Human.Trace.UnifiedReduced.Proth120Permutation
public import Human.Compiler.Proth120Native

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120
open Trace

def NativeRowEvidence (trace : WrapTrace) (initial : RV.State) (row : Row proth120Modulus Kind) : Prop :=
  ∃ (publicRows : PublicLookupRows trace.rom (PublicDecode {initial with pc := row.start.word.toBitVec} (isRead row))) (physical : GKRAddress → F),
    NativeArithmetic physical row.assignment ∧ NativeLookupsMatched publicRows.generic physical

structure NativeTraceInputs (trace : WrapTrace) (initial : RV.State) (cells : List Cell) : Prop
    extends TraceBoundary trace initial cells where
  permutation : WrapPermutation trace
  rows : ∀ row ∈ trace.rows,
    let pc := row.start.word.toBitVec
    pc.toNat % 4 = 0 ∧ pc.toNat + 4 ≤ romEnd ∧ row.assignment row.columns.execute = 1 ∧
      NativeRowEvidence trace initial row

/-- Sparse native gates and public lookup operands, with matched state and RAM permutations,
    imply a complete wrap execution from the public state to the terminal register/RAM tokens. -/
def NativeTraceSoundnessClaim : Prop :=
  ∀ trace initial cells, NativeTraceInputs trace initial cells → TraceResult trace initial cells

def NativeTraceSoundnessSatisfiableClaim : Prop :=
  ∃ (trace : WrapTrace) (initial : RV.State) (cells : List Cell), NativeTraceInputs trace initial cells ∧ trace.rows ≠ []

end Airbender.UnifiedReduced.Proth120
