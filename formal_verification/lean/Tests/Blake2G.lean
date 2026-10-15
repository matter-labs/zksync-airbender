import Airbender.Proofs.Blake2G
import Airbender.Proofs.BabyBear
import Airbender.Proofs.Blake2G.Tables
import Airbender.Proofs.Blake2G.Claims
import Mathlib.Tactic.IntervalCases

namespace Tests.Blake2G
open Airbender

/-- The reusable fragment still enforces the actual output assembly equation.
    This malformed assignment has a nonzero output and zero mixing inputs. -/
theorem wrongMixingOutputRejected (setup : Table (ZMod babyBearModulus) (fields 9)) :
    ¬ FlatOperation.ConstraintsHoldFlat
      (Verification.environment (fun column => if column = 17 then 1 else 0))
      (Blake2G.Proofs.mixingConstraints setup) := by
  intro holds
  have output := Verification.assertion_of_holds holds
    ⟨0, by rw [Blake2G.Proofs.mixing_constraint_count]; decide⟩
  norm_num [Blake2G.Proofs.mixingConstraints, Blake2G.importedConstraints,
    FlatOperation.constraints, Expression.eval, Verification.environment] at output

private def rowInput : Blake2G.Row.Input :=
  ⟨⟨⟨0, by decide⟩, true⟩, ⟨0, 0⟩, ⟨0, 0⟩,
    Vector.replicate 16 ⟨0, 0⟩, Vector.replicate 16 ⟨0, 0⟩⟩

private def wrongRowAddress : Blake2G.Row.Output :=
  ⟨Blake2G.Control.step rowInput.controller, Vector.replicate 16 ⟨0, 0⟩,
    #v[4, 16, 32, 48, 0, 4]⟩

/-- Wrong address rejected through the primary row claim, for any assignment.
    This checks the composed interface, not global memory-argument enforcement. -/
theorem wrongRowAddressRejected (w : Nat → ZMod babyBearModulus) :
    ¬ (Blake2G.Row.InterfaceAssumptions rowInput wrongRowAddress w ∧
      Blake2G.Row.circuitModel.relation rowInput wrongRowAddress w) := by
  intro row
  have correct := Blake2G.Row.babyBear_soundness rowInput wrongRowAddress w row
  have addresses := correct.2.2
  have first := congrArg (fun a : Blake2G.Addresses.Output => a[0]) addresses
  simp [rowInput, wrongRowAddress, Blake2G.Row.addressInput, Blake2G.Addresses.expected,
    Blake2G.Control.step, Blake2G.Control.stateLanes, Arithmetic.Word.toBitVec,
    Arithmetic.Word.value] at first

-- Actual fourth state port, last word of the highest aligned 64-byte block.
theorem lastLaneAddress : (Blake2G.importedConstraintsIndirectPorts[3]).address
    (fun column => if column = 13 then (65472 : ZMod babyBearModulus)
      else if column = 14 then 65535 else if column = 10 then 15 else 0) =
    (0xfffffffc : BitVec 32) := by decide

/-- The imported controller excludes two state ports selecting the same lane,
    on active rows within the eight-bit ABI domain. -/
theorem aliasedStateLanesRejected {input : Blake2G.State.Input} {output : Blake2G.State.Output}
    {w : Nat → ZMod babyBearModulus} (sameLane : input.lanes[0] = input.lanes[1])
    (active : w Blake2G.Variables.execute = 1)
    (bound : (w Blake2G.Variables.controlReadLo).val < 256) :
    ¬ Blake2G.State.circuitModel.relation input output w := by
  intro ⟨holds, mapping⟩
  have distinct := Blake2G.State.Proofs.selected_distinct (by decide) holds mapping active bound
  have different := (List.pairwise_iff_getElem.mp distinct) 0 1 (by simp) (by simp) (by decide)
  exact different sameLane

-- Boundary values from the Rust controller schedule: last full/reduced calls,
-- out-of-schedule fallback, and inactive-row clearing.
example : Blake2G.Control.step ⟨⟨79, by decide⟩, true⟩ =
    ⟨⟨0, 0⟩, #v[3, 4, 9, 14], #v[13, 0]⟩ := by decide

example : Blake2G.Control.step ⟨⟨183, by decide⟩, true⟩ =
    ⟨⟨128, 0⟩, #v[3, 4, 9, 14], #v[8, 11]⟩ := by decide

example : Blake2G.Control.step ⟨⟨127, by decide⟩, true⟩ =
    ⟨⟨0, 0⟩, #v[0, 4, 8, 12], #v[0, 1]⟩ := by decide

example : Blake2G.Control.step ⟨⟨255, by decide⟩, false⟩ =
    ⟨⟨0, 0⟩, #v[0, 0, 0, 0], #v[0, 0]⟩ := by decide

private def wrongControlQuery : Lookup (ZMod babyBearModulus) where
  table := (Blake2G.setupTable Blake2G.Control.controllerRows).toRaw
  -- Key 335 is active/full-mode counter 79. The next counter must be zero.
  entry := #v[.const 335, .const 1, .const 3, .const 4, .const 9, .const 14,
    .const 13, .const 0, .const 28]

private theorem lastFullNextZero : (Blake2G.Control.controllerRows (335 : Fin 512))[(0 : Fin 7)] = 0 := by
  decide +kernel

theorem wrongControlWriteRejected : ¬ wrongControlQuery.Contains
    (Verification.environment (fun _ => 0)) := by
  intro member
  obtain ⟨key, input, columns⟩ := Blake2G.Proofs.control_lookup (by decide) member (by rfl)
  have inputValue := congrArg ZMod.val input
  have keyBound : key.val < babyBearModulus := by have size := key.isLt; dsimp [babyBearModulus]; omega
  have literal : (335 : ZMod babyBearModulus).val = 335 := by decide
  change (335 : ZMod babyBearModulus).val = (key.val : ZMod babyBearModulus).val at inputValue
  rw [literal, ZMod.val_natCast_of_lt keyBound] at inputValue
  have keyEqual : key = (335 : Fin 512) := Fin.ext inputValue.symm
  have output := columns 0
  rw [keyEqual] at output
  change (1 : ZMod babyBearModulus) =
    ((Blake2G.Control.controllerRows (335 : Fin 512))[(0 : Fin 7)] : ZMod babyBearModulus) at output
  rw [lastFullNextZero] at output
  change (1 : ZMod babyBearModulus) = 0 at output
  exact (by decide : (1 : ZMod babyBearModulus) ≠ 0) output

-- This remains impossible regardless of the externally supplied setup contents.
example {setup : Table (ZMod babyBearModulus) (fields 9)} {w : Nat → ZMod babyBearModulus}
    (unaligned : w 13 = 1) :
    ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Blake2G.importedConstraints setup) := by
  intro holds
  have aligned := Blake2G.Proofs.pointer_alignment (by decide) (by decide) holds
  rw [unaligned] at aligned
  have value : (1 : ZMod babyBearModulus).val = 1 := by decide
  rw [value] at aligned
  norm_num at aligned

example {setup : Table (ZMod babyBearModulus) (fields 9)} {w : Nat → ZMod babyBearModulus}
    (nonzero : w 4 ≠ 0) :
    ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Blake2G.importedConstraints setup) := by
  intro holds
  exact nonzero (Blake2G.Proofs.control_high_zero holds).1

private def control (_ : Fin 512) : Vector Nat 7 := Vector.replicate 7 0

private def chunkQuery (a b c tag : Nat) : Lookup (ZMod babyBearModulus) where
  table := (Blake2G.setupTable control).toRaw
  entry := #v[.const (a : ZMod babyBearModulus), .const (b : ZMod babyBearModulus),
    .const (c : ZMod babyBearModulus), .const 0, .const 0, .const 0, .const 0,
    .const 0, .const (tag : ZMod babyBearModulus)]

private def emptyEnv : Environment (ZMod babyBearModulus) := Verification.environment (fun _ => 0)

-- A maximum-width boundary pair has a real row in the modeled static setup.
example : (chunkQuery 511 256 255 20).Contains emptyEnv := by
  change ∃ i : Fin 344896,
    ((chunkQuery 511 256 255 20).entry.map (Expression.eval emptyEnv)) =
      (Blake2G.setupRow control i).map (fun (n : Nat) => (n : ZMod babyBearModulus))
  refine ⟨⟨82240 + 511 * 512 + 256, by decide⟩, ?_⟩
  have row : Blake2G.setupRow control ⟨82240 + 511 * 512 + 256, by decide⟩ =
      #v[511, 256, 255, 0, 0, 0, 0, 0, 20] := by decide
  rw [row]
  change (Vector.map (Expression.eval emptyEnv)
    (#v[.const (511 : ZMod babyBearModulus), .const 256, .const 255,
      .const 0, .const 0, .const 0, .const 0, .const 0, .const 20] :
      Vector (Expression (ZMod babyBearModulus)) 9)) =
    (#v[511, 256, 255, 0, 0, 0, 0, 0, 20] : Vector Nat 9).map
      (fun (n : Nat) => (n : ZMod babyBearModulus))
  apply Vector.ext
  intro j hj
  rw [Vector.getElem_map, Vector.getElem_map]
  interval_cases j <;> rfl

-- The first out-of-range input is rejected by table membership itself.
example : ¬ (chunkQuery 512 0 512 20).Contains emptyEnv := by
  intro member
  have result := Blake2G.Proofs.xor_lookup (by decide) 4 member (by simp [Expression.eval])
  have value : (512 : ZMod babyBearModulus).val = 512 := by decide
  have bound : (512 : ZMod babyBearModulus).val < 512 := by
    simpa [Expression.eval] using result.1
  rw [value] at bound
  omega

-- In-range inputs with the wrong XOR cannot be accepted either.
example : ¬ (chunkQuery 7 3 5 4).Contains emptyEnv := by
  intro member
  have result := Blake2G.Proofs.xor_lookup (by decide) 0 member (by simp [Expression.eval])
  have equation : (5 : ZMod babyBearModulus).val =
      (7 : ZMod babyBearModulus).val ^^^ (3 : ZMod babyBearModulus).val := by
    simpa [Expression.eval] using result.2.2.2
  have wrong : ¬ (5 : ZMod babyBearModulus).val =
      (7 : ZMod babyBearModulus).val ^^^ (3 : ZMod babyBearModulus).val := by decide
  exact wrong equation

end Tests.Blake2G
