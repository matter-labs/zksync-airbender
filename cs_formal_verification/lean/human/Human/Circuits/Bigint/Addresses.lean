import Human.Circuits.Bigint.Artifact
import Human.Circuits.Bigint.Tables.Setup
import Human.Helpers.Properties

namespace Airbender.Bigint.Addresses
open Arithmetic

structure Input where
  left : Word
  right : Word

abbrev Output := Vector (BitVec 32) 16

def expected (input : Input) : Output :=
  (Vector.ofFn fun i : Fin 8 => input.left.toBitVec + BitVec.ofNat 32 (4 * i.val)).append
    (Vector.ofFn fun i : Fin 8 => input.right.toBitVec + BitVec.ofNat 32 (4 * i.val))

/-- Address projection of `riscv_transpiler/src/vm/delegations/bigint.rs`.
    Global memory transport remains external.
    Both pointer alignments are established by native scaled-range queries. -/
def spec (input : Input) (output : Output) : Prop :=
  input.left.lo % 32 = 0 ∧ input.right.lo % 32 = 0 ∧ output = expected input

structure Mapping {p : Nat} (input : Input) (output : Output) (w : Nat → ZMod p) : Prop where
  left : input.left = ⟨(w 3).val, (w 4).val⟩
  right : input.right = ⟨(w 37).val, (w 38).val⟩
  addresses : output = importedConstraintsIndirectPorts.map (fun port => port.address w)

/-- Canonical pointer limbs remain a register-interface obligation. Distinct
    pointers and RAM-only access belong to the full call, not this projection. -/
def InterfaceAssumptions (input : Input) (_output : Output) (_w : Nat → ZMod p) : Prop :=
  input.left.Bounded ∧ input.right.Bounded

def circuitModel {p : Nat} [Fact p.Prime] :
    Verification.CircuitModel Input Output (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (importedConstraints setupTable)
  represents := Mapping

end Airbender.Bigint.Addresses
