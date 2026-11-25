module
public import Human.Circuits.AddSub.Modular.Model
public import Human.Circuits.UnifiedReduced.Artifact
public import Human.Helpers.Core.CircuitField

@[expose] public section
namespace Airbender.UnifiedReduced.Modular
open Arithmetic AddSub.Modular

/-- The host stores both 16-bit limbs of each architectural word in consecutive columns. -/
def wordAt {p : Nat} (w : Nat → ZMod p) (i : Nat) : Word := ⟨(w i).val, (w (i + 1)).val⟩

abbrev Operations (p : Nat) [CircuitField p] := Table (ZMod p) (fields 10) → List (FlatOperation (ZMod p))

/-- All four decoded modular branches use these source words and output columns in both layouts. -/
def RowProperty (p : Nat) [CircuitField p] (ops : Operations p)
    (property : Opcode → Word → Word → Word → Word → Prop) : Prop :=
  ∀ setup (w : Nat → ZMod p) (op : Opcode),
    FlatOperation.ConstraintsHoldFlat (Verification.environment w) (ops setup) →
    (∀ k, 11 ≤ k → k ≤ 20 → w k = if k = op.selector + 1 then 1 else 0) →
    (wordAt w 36).Bounded → (wordAt w 42).Bounded → (wordAt w 48).Bounded →
    property op (wordAt w 36) (wordAt w 42) (wordAt w 48) (wordAt w 50)

/-- A host layout's equations prove a canonical representative and its residue in the RV guest field. -/
def ResultCertificate (p : Nat) [CircuitField p] (ops : Operations p) : Prop :=
  RowProperty p ops fun op left right old out =>
    out.value < babyBearModulus ∧ (out.value : ZMod babyBearModulus) =
      arithmeticResult op left.toBitVec right.toBitVec old.toBitVec

/-- The host circuit writes the result of the guest RV32 BabyBear instruction. -/
def ResultSoundness (p : Nat) [CircuitField p] (ops : Operations p) : Prop :=
  RowProperty p ops fun op left right old out =>
    out.toBitVec = RV.mopVal op.rvOp left.toBitVec right.toBitVec old.toBitVec

/-- An active row witnesses the same layout and premise types as the soundness theorem. -/
def RowSatisfiable (p : Nat) [CircuitField p] (ops : Operations p) : Prop :=
  ∃ (setup : Table (ZMod p) (fields 10)) (w : Nat → ZMod p) (op : Opcode),
    FlatOperation.ConstraintsHoldFlat (Verification.environment w) (ops setup) ∧
    (∀ k, 11 ≤ k → k ≤ 20 → w k = if k = op.selector + 1 then 1 else 0) ∧
    (wordAt w 36).Bounded ∧ (wordAt w 42).Bounded ∧ (wordAt w 48).Bounded ∧ w 4 = 1

/-- The native BabyBear layout as an instance of the common RV instruction contract. -/
def BabyBearResultClaim : Prop := ResultSoundness babyBearModulus importedConstraints
def BabyBearResultSatisfiableClaim : Prop := RowSatisfiable babyBearModulus importedConstraints

end Airbender.UnifiedReduced.Modular
