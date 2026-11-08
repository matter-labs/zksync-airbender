module
public import Human.Helpers.Memory.InitialImage
public import Human.Helpers.Memory.ROM

@[expose] public section

-- These definitions are specifications, read by proofs, never executed.
noncomputable section

namespace Airbender.Trace
open Arithmetic

/-- Native decoder fields, not instruction behavior. The preprocessing follows
    `cs/src/gkr_circuits/{add_sub_family,mem_word_only}/decoder.rs`. -/
structure DecoderData (Kind : Type := Family) where
  /-- Circuit family selected by native instruction preprocessing. -/
  family : Kind
  rs1 : BitVec 5
  rs2 : BitVec 5
  rd : BitVec 5
  /-- Native immediate limbs, including sign extension or other family preprocessing. -/
  immediate : Word
  /-- Packed selector bits used by the native decoder lookup. -/
  mask : Nat
  /-- Family-specific operation tag; zero when no such column is used. -/
  funct3 : Nat := 0

def arithmeticFields (rs1 rs2 rd : BitVec 5) (immediate : BitVec 32)
    (mask : Nat) : DecoderData :=
  if rd = 0 then ⟨.addSub, 0, 0, 0, ⟨0, 0⟩, 1, 0⟩
  else ⟨.addSub, rs1, rs2, rd, Word.ofBitVec immediate, mask, 0⟩

/-- Change only the circuit registry tag; native metadata is retained
    verbatim. -/
def DecoderData.mapFamily {Kind Target : Type} (f : Kind → Target)
    (data : DecoderData Kind) : DecoderData Target :=
  ⟨f data.family, data.rs1, data.rs2, data.rd, data.immediate, data.mask, data.funct3⟩

/-- The active native decoder query, using only imported column descriptors.
    The missing funct3 column is zero; selector bits are packed as in Rust. -/
def nativeDecoderQuery {p : Nat} (columns : TraceColumns) (c : DecoderColumns)
    (w : Nat → ZMod p) : Vector (ZMod p) 9 :=
  #v[w columns.initialPC[0], w columns.initialPC[1], w c.rs1, w c.rs2,
    w c.rd, w c.immediate[0], w c.immediate[1], c.funct3.map w |>.getD 0,
    ∑ i : Fin c.flags.size, (2 ^ i.val : Nat) * w c.flags[i]]

noncomputable abbrev Row.decoderQuery {Kind : Type} [CircuitLayout Kind] (row : Row p Kind) : Vector (ZMod p) 9 :=
  nativeDecoderQuery row.columns row.decoderColumns row.assignment

def Row.decoderImmediate {Kind : Type} [CircuitLayout Kind] (row : Row p Kind) : Word :=
  ⟨(row.assignment row.decoderColumns.immediate[0]).val,
    (row.assignment row.decoderColumns.immediate[1]).val⟩

end Airbender.Trace
