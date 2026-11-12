module
public import Human.Helpers.Delegation.SpanABI
public import Human.Trace.Workers.Blake2G.WorkVector
public import Proven.Delegation.NativeSegments
public import Proven.Keccak.CallPermutation
public import Mathlib.Tactic.IntervalCases
public import Proven.Defs.Circuits.Keccak.Artifact
public import Proven.Defs.Circuits.Keccak.Theta

@[expose] public section

namespace Tests.KeccakTheta
open Airbender
set_option warningAsError true
set_option maxRecDepth 16384

-- A supplied controller row makes the local arithmetic test independent of
-- the still-open controller schedule and global memory argument.
def control (_ : Fin 4096) : Vector Nat 6 := #v[0, 5, 10, 15, 20, 25]

abbrev setup : Table (ZMod babyBearModulus) (fields 8) := Keccak.setupTable control

def row (v : Nat) : ZMod babyBearModulus :=
  if v = 0 ∨ v = 66 ∨ v = 70 then 1
  else if v = 3 then 3 else if v = 5 then 11
  else if 7 ≤ v ∧ v < 13 then (5 * (v - 7) : Nat)
  else if 15 ≤ v ∧ v < 63 then
    let lane := (v - 15) / 8
    let limb := ((v - 15) % 8) / 4 * 2 + (v - 15) % 2
    let shared : Nat := if limb = 0 then 1 else if limb = 3 then 256 else 0
    ((if lane = 5 then shared
    else if (v - 15) % 4 < 2 then 65535 else 65535 ^^^ shared : Nat) : ZMod babyBearModulus)
  else if v = 86 then 8192 else if v = 87 then 24640
  else if v = 88 then 41088 else if v = 89 then 57536
  else if 102 ≤ v ∧ v < 222 then
    let col := ((v - 102) % 24) / 8
    let byte := (v - 102) % 8
    let shared : Nat := if byte = 0 ∨ byte = 7 then 1 else 0
    ((if col = 0 then 255 else if col = 1 then shared else 255 ^^^ shared : Nat) : ZMod babyBearModulus)
  else 0

private theorem modes (j : Fin 7) : row Keccak.Variables.modeColumns[j] = if j = 3 then 1 else 0 := by
  fin_cases j <;> decide

-- Every Theta byte query XORs the all-ones lane with the shared word `0x0100000000000001`.

-- These values are read from the native ports after proving the full row holds.
theorem nativeLaneValues : Keccak.readLane row 0 = 18446744073709551615 ∧
    Keccak.readLane row 5 = 72057594037927937 ∧
    Keccak.writeLane row 0 = 18374686479671623678 := by decide

theorem wrongWriteRejected {w : Nat → ZMod babyBearModulus}
    (active : w 0 = 1) (theta : w 66 = 1)
    (source : Keccak.readLane w 0 = 18446744073709551615)
    (scratch : Keccak.readLane w 5 = 72057594037927937)
    (wrong : Keccak.writeLane w 0 = 18374686479671623679) :
    ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Keccak.importedConstraints setup) := by
  intro holds
  have equation := (Keccak.Proofs.theta_lane_xor (by decide) holds active theta (0 : Fin 5)).2.2.2
  change Keccak.writeLane w (0 : Fin 6) =
    Keccak.readLane w (0 : Fin 6) ^^^ Keccak.readLane w (5 : Fin 6) at equation
  rw [source, scratch, wrong] at equation
  exact (by decide : ¬ 18374686479671623679 = 18446744073709551615 ^^^ 72057594037927937) equation

private theorem controllerBounded : ∀ key : Fin 4096, ∀ i : Fin 6, (control key)[i] < 31 := by
  intro key
  change ∀ i : Fin 6, (#v[0, 5, 10, 15, 20, 25] : Vector Nat 6)[i] < 31
  decide

-- Elaborated at reducible transparency: `ByteLookupChecks` unfolds to a Pi, and the default
-- elaboration whnf-evaluates every byte query of the concrete row (about 20 s).

-- At the last aligned low-limb block, even the largest modeled lane index
-- and its high word remain below the limb boundary.
theorem boundaryNoCarry : 65280 + 8 * 30 + 4 < Arithmetic.limbBase := by decide

end Tests.KeccakTheta
