import Slop.AddSub.ArtifactChecks
import Slop.AddSub.SailContract
import Human.Helpers.Properties

namespace Airbender.AddSub
open Airbender.Reference.RiscV
open Airbender.Arithmetic

-- Internal row-calculation interfaces. Integrated traces derive these from
-- actual decoding and initialized history in Proofs/Trace/Arithmetic.lean.

/-- Shared decoder preprocessing for standalone and unified arithmetic rows. -/
abbrev Preprocessing (input : Sail.Input) : Prop :=
  if input.rd = Sail.zeroRegister then
    input.row.left = ⟨0, 0⟩ ∧ input.row.right = ⟨0, 0⟩ ∧ input.row.immediate = ⟨0, 0⟩
  else match input.row.opcode with
    | .add | .sub => input.row.immediate = ⟨0, 0⟩
    | .addi => input.row.right = ⟨0, 0⟩
    | .lui | .auipc => input.row.left = ⟨0, 0⟩ ∧ input.row.right = ⟨0, 0⟩

/-- Decoded standard row; writes to x0 select ADD with zero operands, as specified
    by Airbender's preprocessing. The original instruction tag remains unchanged in Sail. -/
structure DecoderContract {F : Type} [Field F] (input : Sail.Input) (w : Nat → F) : Prop where
  active : w 4 = 1
  addSelector : w 10 = if input.rd = Sail.zeroRegister then 1
    else if input.row.opcode = .sub ∨ input.row.opcode = .auipc then 0 else 1
  subSelector : w 11 = if input.rd ≠ Sail.zeroRegister ∧ input.row.opcode = .sub then 1 else 0
  otherSelectors : ∀ k, 12 ≤ k → k ≤ 18 →
    w k = if input.rd ≠ Sail.zeroRegister ∧ input.row.opcode = .auipc ∧ k = 12 then 1 else 0
  preprocessing : Preprocessing input

/-- Hypotheses for the arithmetic calculation, derived from initialized
    history and actual decoder membership by the integrated trace proof. -/
structure InputBounds (input : RowInput) : Prop where
  leftBound : input.left.Bounded
  rightBound : input.right.Bounded
  immediateBound : input.immediate.Bounded

/-- Inputs encode declared limbs and the destination index; outputs decode canonical prime-field values.
    This supplies no 16-bit bounds and no arithmetic conclusion. -/
structure RowWordMapping {p : Nat} (input : Sail.Input) (output : Sail.Output)
    (w : Nat → ZMod p) : Prop where
  leftLo : w 25 = (input.row.left.lo : ZMod p)
  leftHi : w 26 = (input.row.left.hi : ZMod p)
  rightLo : w 29 = (input.row.right.lo : ZMod p)
  rightHi : w 30 = (input.row.right.hi : ZMod p)
  immediateLo : w 8 = (input.row.immediate.lo : ZMod p)
  immediateHi : w 9 = (input.row.immediate.hi : ZMod p)
  pcLo : w 0 = (input.row.pc.lo : ZMod p)
  pcHi : w 1 = (input.row.pc.hi : ZMod p)
  destinationIndex : match input.rd with
    | .Regidx bits => w 7 = (bits.toNat : ZMod p)
  outputLo : output.destination.lo = (w 33).val
  outputHi : output.destination.hi = (w 34).val
  finalPCLo : output.pc.lo = (w 19).val
  finalPCHi : output.pc.hi = (w 20).val

/-- Local view of the imported Clean constraints used by calculation lemmas. -/
def rowCircuitModel {p : Nat} [Fact p.Prime] :
    Verification.CircuitModel Sail.Input Sail.Output (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints
  represents := fun input output w => RowWordMapping input output w

/-- Internal obligations discharged by the trace proof before using row soundness. -/
structure RowInterfaces {p : Nat} [Fact p.Prime] (input : Sail.Input)
    (_output : Sail.Output) (w : Nat → ZMod p) : Prop where
  decoder : DecoderContract input w
  ranges : input.rd ≠ Sail.zeroRegister → InputBounds input.row
  initialPCBounds : input.row.pc.Bounded
  registers : Sail.Contract input

/-! Row-level twins over `(row, rd)`, for callers that have no Sail input (the RV integration). The Sail
    definitions above are unchanged; the bridges below turn each Sail statement into its row-level twin. -/

/-- The five-bit destination index of a Sail register index. -/
def rdBits : SailRV32.regidx → BitVec 5
  | .Regidx bits => bits

theorem rd_eq_zero_iff (r : SailRV32.regidx) : r = Sail.zeroRegister ↔ rdBits r = 0 := by
  cases r with
  | Regidx bits => simp [rdBits, Sail.zeroRegister]

theorem rd_ne_zero {r : SailRV32.regidx} (h : r ≠ Sail.zeroRegister) : rdBits r ≠ 0 :=
  fun hb => h ((rd_eq_zero_iff r).mpr hb)

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
structure RowWordMappingRow {p : Nat} (row : RowInput) (rd : BitVec 5) (output : Sail.Output)
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

theorem preprocessing_toRow {input : Sail.Input} (h : Preprocessing input) :
    PreprocessingRow input.row (rdBits input.rd) := by
  unfold Preprocessing at h
  unfold PreprocessingRow
  simp only [rd_eq_zero_iff] at h
  exact h

theorem DecoderContract.toRow {F : Type} [Field F] {input : Sail.Input} {w : Nat → F}
    (dc : DecoderContract input w) : DecoderContractRow input.row (rdBits input.rd) w where
  active := dc.active
  addSelector := by simpa only [rd_eq_zero_iff] using dc.addSelector
  subSelector := by simpa only [rd_eq_zero_iff, ne_eq] using dc.subSelector
  otherSelectors := fun k h1 h2 => by
    simpa only [rd_eq_zero_iff, ne_eq] using dc.otherSelectors k h1 h2
  preprocessing := preprocessing_toRow dc.preprocessing

theorem RowWordMapping.toRow {p : Nat} {input : Sail.Input} {output : Sail.Output} {w : Nat → ZMod p}
    (m : RowWordMapping input output w) : RowWordMappingRow input.row (rdBits input.rd) output w := by
  have key : ∀ r : SailRV32.regidx, (match r with
      | .Regidx bits => w 7 = (bits.toNat : ZMod p)) → w 7 = ((rdBits r).toNat : ZMod p) := by
    intro r h
    cases r
    exact h
  exact {
    leftLo := m.leftLo, leftHi := m.leftHi, rightLo := m.rightLo, rightHi := m.rightHi,
    immediateLo := m.immediateLo, immediateHi := m.immediateHi, pcLo := m.pcLo, pcHi := m.pcHi,
    destinationIndex := key input.rd m.destinationIndex,
    outputLo := m.outputLo, outputHi := m.outputHi, finalPCLo := m.finalPCLo, finalPCHi := m.finalPCHi }

end Airbender.AddSub
