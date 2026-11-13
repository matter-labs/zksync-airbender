module
public import Human.Circuits.Bigint.Memory
public import Proven.Bigint.Addresses
public import Proven.Bigint.NativeExecution
public import Proven.Bigint.WitnessCheck
public import Proven.KernelRfl
public import Proven.Defs.Circuits.Bigint.Additive

@[expose] public section

namespace Tests.Bigint
open Airbender

def zeroSetup : Table (ZMod babyBearModulus) (fields 3) := Bigint.setupTable

namespace Additive
open Airbender.Bigint.Additive

def zero : Vector Nat 16 := Vector.replicate 16 0
def maximum : Vector Nat 16 := Vector.replicate 16 65535
def one : Vector Nat 16 := Vector.ofFn fun i => if i.val = 0 then 1 else 0

-- A concrete all-zero ADD row checks the full imported relation against
-- the modeled production setup; no source-range premise is supplied.
def zeroAddRow : Nat → ZMod babyBearModulus
  | 0 | 55 | 59 | 212 | 214 | 215 => 1
  | _ => 0

theorem zeroAddSatisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment zeroAddRow)
      (Bigint.importedConstraints zeroSetup) :=
  Bigint.holds_of_check (by kernel_rfl)

-- Boundary cases of the project's pure custom arithmetic reference.
example : spec ⟨.add, maximum, maximum, true⟩ ⟨maximum, ⟨1, 0⟩⟩ := by unfold spec; decide
example : spec ⟨.sub, zero, one, false⟩ ⟨maximum, ⟨1, 0⟩⟩ := by unfold spec; decide
example : spec ⟨.reverseSub, one, zero, false⟩ ⟨maximum, ⟨1, 0⟩⟩ := by unfold spec; decide
example : spec ⟨.copy, zero, maximum, true⟩ ⟨zero, ⟨1, 0⟩⟩ := by unfold spec; decide

/-- The modeled fixed table rejects an oversized source without an external
    range premise; this exercises the native query-to-port mapping. -/
theorem sourceOverflowRejected (input : Input) (output : Bigint.Output)
    (w : Nat → ZMod babyBearModulus) (i : Fin 16)
    (oversized : Arithmetic.limbBase ≤ input.left[i]) :
    ¬ (circuitModel Bigint.setupTable).relation input output w := by
  intro ⟨h, mapping⟩
  have bounded := (Bigint.Proofs.mapped_source_ranges (by decide) h mapping.left mapping.right).1 i
  omega

end Additive
namespace Equality
open Airbender.Bigint.Equality

def zero : Vector Nat 16 := Vector.replicate 16 0

-- Incoming carry is set, but EQ must ignore it and still report equality.
def equalRow : Nat → ZMod babyBearModulus
  | 55 => 96
  | 0 | 57 | 64 | 65 | 212 | 214 | 215 | 216 => 1
  | _ => 0

theorem equalSatisfies :
    FlatOperation.ConstraintsHoldFlat (Verification.environment equalRow)
      (Bigint.importedConstraints zeroSetup) :=
  Bigint.holds_of_check (by kernel_rfl)

end Equality
end Tests.Bigint
