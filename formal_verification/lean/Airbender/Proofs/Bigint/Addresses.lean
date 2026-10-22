import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.Bigint.ArtifactChecks
import Airbender.Review.Circuits.Bigint.Addresses
import Airbender.Proofs.MemoryPorts
import Airbender.Proofs.Constraints
import Airbender.Proofs.Lookups
import Airbender.Proofs.Arithmetic.Chunks
import Airbender.Proofs.BabyBear
import Airbender.Proofs.Trace.Timestamps
import Mathlib.Tactic.LinearCombination

namespace Airbender.Bigint.Addresses.Proofs
open Arithmetic
set_option warningAsError true
set_option maxHeartbeats 800000
set_option maxRecDepth 16384

theorem pointer_alignment {p : Nat} [Fact p.Prime] (_hp : FieldCapacity.AtLeast p 2097152)
    (inverse : SerializedInverse.Scale32 p) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    (w 3).val % 32 = 0 ∧ (w 37).val % 32 = 0 := by
  have characteristic : (babyBearModulus : ZMod p) = 0 := by
    unfold babyBearModulus
    linear_combination -inverse
  have field := babyBear_eq_of_natCast_zero characteristic
  have capacity : 32 * Trace.timestampBase ≤ p := by rw [field]; decide
  have left := Trace.Proofs.range_bound
    (Verification.lookup_of_holds h ⟨32, by rw [lookup_count]; decide⟩)
  have right := Trace.Proofs.range_bound
    (Verification.lookup_of_holds h ⟨33, by rw [lookup_count]; decide⟩)
  simp [Expression.eval, Verification.environment, ] at left right
  have lv := value_of_scaled_range capacity (by decide) inverse
    (by simpa only [neg_mul] using left)
  have rv := value_of_scaled_range capacity (by decide) inverse
    (by simpa only [neg_mul] using right)
  constructor <;> first | (rw [lv]; simp) | (rw [rv]; simp)

theorem soundness {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 2097152)
    (inverse : SerializedInverse.Scale32 p) :
    (circuitModel (p := p)).SoundnessUnder InterfaceAssumptions spec := by
  intro input output w ⟨bounds, h, mapping⟩
  have align := pointer_alignment hp inverse h
  have leftAligned : input.left.lo % 32 = 0 := by rw [mapping.left]; exact align.1
  have rightAligned : input.right.lo % 32 = 0 := by rw [mapping.right]; exact align.2
  refine ⟨leftAligned, rightAligned, ?_⟩
  have mapAppend (a b : Vector Verification.IndirectPort 8) :
      (a.append b).map (fun port => port.address w) =
        (a.map (fun port => port.address w)).append (b.map (fun port => port.address w)) :=
    Vector.map_append
  rw [mapping.addresses, port_layout, mapAppend]
  unfold expected
  apply congrArg₂ (fun a b : Vector (BitVec 32) 8 => a.append b)
  all_goals apply Vector.ext
  all_goals intro i hi
  all_goals simp only [Vector.getElem_map, Vector.getElem_ofFn]
  · apply Verification.IndirectPort.constant_address (by omega) rfl mapping.left
    exact Verification.block_offset_bound (block := 32) (by decide) bounds.1.1 leftAligned (by change 4 * i < 32; omega)
  · apply Verification.IndirectPort.constant_address (by omega) rfl mapping.right
    exact Verification.block_offset_bound (block := 32) (by decide) bounds.2.1 rightAligned (by change 4 * i < 32; omega)

end Airbender.Bigint.Addresses.Proofs
