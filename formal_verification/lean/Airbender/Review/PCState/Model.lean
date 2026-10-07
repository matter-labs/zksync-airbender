import Airbender.Review.RangeChecks
import Mathlib.Data.List.Perm.Basic

namespace Airbender.PCState

/-- The PC columns of a supported decoder row or a public boundary state. -/
def encode {p : Nat} (pc : BitVec 32) : ZMod p × ZMod p :=
  ((pc.toNat % Arithmetic.limbBase : Nat), (pc.toNat / Arithmetic.limbBase : Nat))

/-- Projection of Rust's decoder rows onto their two PC columns. Unsupported
    entries contain `-1` in both columns. The program/setup binding is external;
    this is a modeled projection, not an extracted decoder artifact.
    Source: cs/src/gkr_circuits/decoder_trait.rs. -/
def decoderRow {p : Nat} (pc : Option (BitVec 32)) : ZMod p × ZMod p :=
  match pc with
  | some pc => encode pc
  | none => (-1, -1)

def decoderTable {p n : Nat} [Fact p.Prime]
    (program : Vector (Option (BitVec 32)) n) : Table (ZMod p) fieldPair := .fromStatic {
  name := "Airbender.DecoderPCProjection"
  length := n
  row i := decoderRow program[i]
  index pc := program.toArray.findIdx fun entry => decoderRow entry == pc
  Spec pc := ∃ i : Fin n, pc = decoderRow program[i]
  contains_iff _ := Iff.rfl
}

/-- The state permutation keeps both PC limbs and both timestamp columns.
    Only active execution rows belong to the lists below. -/
structure State (p : Nat) where
  pc : ZMod p × ZMod p
  timestamp : ZMod p × ZMod p

def boundary {p : Nat} (pc : BitVec 32) (timestamp : ZMod p × ZMod p) : State p :=
  ⟨encode pc, timestamp⟩

structure Context (p n : Nat) where
  program : Vector (Option (BitVec 32)) n
  initialPC : BitVec 32
  terminalPC : BitVec 32
  initialTimestamp : ZMod p × ZMod p
  terminalTimestamp : ZMod p × ZMod p
  starts : List (State p)
  ends : List (State p)

/-- Logical contracts supplied by the execution argument and decoder lookups.
    Product equality alone is not this contract; its cryptographic justification
    and binding these lists to imported active rows remain separate obligations. -/
structure Interface {p n : Nat} [Fact p.Prime] (context : Context p n) : Prop where
  balanced : (boundary context.initialPC context.initialTimestamp :: context.ends).Perm
    (boundary context.terminalPC context.terminalTimestamp :: context.starts)
  decoded : ∀ state ∈ context.starts, (decoderTable context.program).Contains #[] state.pc

/-- Bind a circuit's outgoing PC columns to an active state-permutation entry. -/
def Outgoing {p n : Nat} (context : Context p n) (pc : ZMod p × ZMod p) : Prop :=
  ∃ state ∈ context.ends, state.pc = pc

end Airbender.PCState
