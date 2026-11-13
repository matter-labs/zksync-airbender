module
public import Human.Circuits.AddSub.RowInput
public import Human.Helpers.Core.CircuitOutput
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.Control.Monad.Writer

@[expose] public section

namespace Airbender.AddSub
open Airbender.Reference.RiscV
open Airbender.Arithmetic

-- Internal row-calculation interfaces. Integrated traces derive these from
-- actual decoding and initialized history in Proofs/Trace/Arithmetic.lean.

/-- Hypotheses for the arithmetic calculation, derived from initialized
    history and actual decoder membership by the integrated trace proof. -/
structure InputBounds (input : RowInput) : Prop where
  leftBound : input.left.Bounded
  rightBound : input.right.Bounded
  immediateBound : input.immediate.Bounded

/-! Row-level twins over `(row, rd)`, for callers that have no Sail input (the RV integration). The Sail
    definitions above are unchanged; the bridges below turn each Sail statement into its row-level twin. -/

/-- Row-level `Preprocessing`: writes to x0 (`rd = 0`) select the NOP row with zero operands. -/
abbrev PreprocessingRow (row : RowInput) (rd : BitVec 5) : Prop :=
  if rd = 0 then
    row.left = ⟨0, 0⟩ ∧ row.right = ⟨0, 0⟩ ∧ row.immediate = ⟨0, 0⟩
  else match row.opcode with
    | .add | .sub => row.immediate = ⟨0, 0⟩
    | .addi => row.right = ⟨0, 0⟩
    | .lui | .auipc => row.left = ⟨0, 0⟩ ∧ row.right = ⟨0, 0⟩

/-- Row-level `DecoderContract`: the same selector equations, with `rd` as five bits. -/
structure DecoderContractRow {F : Type} [Field F] (row : RowInput) (rd : BitVec 5) (w : Nat → F) : Prop where
  active : w 4 = 1
  addSelector : w 10 = if rd = 0 then 1
    else if row.opcode = .sub ∨ row.opcode = .auipc then 0 else 1
  subSelector : w 11 = if rd ≠ 0 ∧ row.opcode = .sub then 1 else 0
  otherSelectors : ∀ k, 12 ≤ k → k ≤ 18 →
    w k = if rd ≠ 0 ∧ row.opcode = .auipc ∧ k = 12 then 1 else 0
  preprocessing : PreprocessingRow row rd

/-- Row-level `RowWordMapping`: the same cell identifications, with the destination as five bits. -/
structure RowWordMappingRow {p : Nat} (row : RowInput) (rd : BitVec 5) (output : Circuit.Output)
    (w : Nat → ZMod p) : Prop where
  leftLo : w 25 = (row.left.lo : ZMod p)
  leftHi : w 26 = (row.left.hi : ZMod p)
  rightLo : w 29 = (row.right.lo : ZMod p)
  rightHi : w 30 = (row.right.hi : ZMod p)
  immediateLo : w 8 = (row.immediate.lo : ZMod p)
  immediateHi : w 9 = (row.immediate.hi : ZMod p)
  pcLo : w 0 = (row.pc.lo : ZMod p)
  pcHi : w 1 = (row.pc.hi : ZMod p)
  destinationIndex : w 7 = (rd.toNat : ZMod p)
  outputLo : output.destination.lo = (w 33).val
  outputHi : output.destination.hi = (w 34).val
  finalPCLo : output.pc.lo = (w 19).val
  finalPCHi : output.pc.hi = (w 20).val

end Airbender.AddSub
