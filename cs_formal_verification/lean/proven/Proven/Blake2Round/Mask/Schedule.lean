module
public import Human.Circuits.Blake2Round.Mask
public import Proven.Blake2Round.Schedule

@[expose] public section
namespace Airbender.Blake2Round.Mask.Proofs
open Arithmetic
open scoped BigOperators

/-- A sum of ten selected 16-bit limbs stays below the wide-message bound. -/
theorem selected_sum_bound (rounds : Fin 10 → Bool) (values : Fin 10 → Nat)
    (bounded : ∀ round, values round < 65536) :
    (∑ round : Fin 10, if rounds round then values round else 0) < 655360 := by
  have term (round : Fin 10) : (if rounds round then values round else 0) < 65536 := by
    split <;> simp_all
  calc
    _ < ∑ _round : Fin 10, (65536 : Nat) :=
      Finset.sum_lt_sum (fun round _ => Nat.le_of_lt (term round)) ⟨0, Finset.mem_univ _, term 0⟩
    _ = 655360 := by norm_num

/-- Every scheduled message limb fits the wider native G interface. -/
theorem scheduled_bounds (rounds : Fin 10 → Bool) (message : Vector Word 16)
    (bounded : ∀ i : Fin 16, message[i].Bounded) (position : Fin 16) :
    (scheduledMessage rounds message)[position].lo < 655360 ∧
      (scheduledMessage rounds message)[position].hi < 655360 := by
  simp only [scheduledMessage, Fin.getElem_fin, Vector.getElem_ofFn]
  constructor
  · apply selected_sum_bound
    intro round
    exact (bounded _).1
  · apply selected_sum_bound
    intro round
    exact (bounded _).2

/-- Imported scheduling equations retain the complete Boolean mask and its wide limb sums. -/
theorem scheduled_messages {w : Nat → ZMod babyBearModulus}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setupTable))
    (rounds : Fin 10 → Bool)
    (bits : ∀ round : Fin 10, w Variables.roundBits[round] = if rounds round then 1 else 0)
    (bounded : ∀ i : Fin 16, (Preparation.messageWords w)[i].Bounded) :
    Preparation.words w Variables.scheduledMessage = scheduledMessage rounds (Preparation.messageWords w) := by
  have equations := Schedule.Proofs.equations constraints
  have coefficient (round : Fin 10) (value : ZMod babyBearModulus) :
      w Variables.roundBits[round] * value =
        ((if rounds round then value.val else 0 : Nat) : ZMod babyBearModulus) := by
    rw [bits]
    split <;> simp_all
  apply Vector.ext
  intro index bound
  let position : Fin 16 := ⟨index, bound⟩
  have canonical := scheduled_bounds rounds (Preparation.messageWords w) bounded position
  obtain ⟨low, high⟩ := equations position
  simp_rw [coefficient] at low high
  rw [← Nat.cast_sum] at low high
  have lowValue := congrArg ZMod.val low
  have highValue := congrArg ZMod.val high
  rw [ZMod.val_natCast_of_lt] at lowValue highValue
  · change (Preparation.words w Variables.scheduledMessage)[position] =
      (scheduledMessage rounds (Preparation.messageWords w))[position]
    simpa only [Preparation.words, scheduledMessage, Preparation.messageWords, Schedule.Proofs.column,
      Fin.getElem_fin, Vector.getElem_map, Vector.getElem_ofFn] using congrArg₂ Word.mk lowValue highValue
  · simpa only [scheduledMessage, Preparation.messageWords, Fin.getElem_fin, Vector.getElem_ofFn,
      Schedule.Proofs.column, position] using canonical.2.trans_le (by decide : 655360 ≤ babyBearModulus)
  · simpa only [scheduledMessage, Preparation.messageWords, Fin.getElem_fin, Vector.getElem_ofFn,
      Schedule.Proofs.column, position] using canonical.1.trans_le (by decide : 655360 ≤ babyBearModulus)

end Airbender.Blake2Round.Mask.Proofs
