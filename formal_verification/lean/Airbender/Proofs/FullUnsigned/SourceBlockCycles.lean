import Airbender.Proofs.FullUnsigned.SourceBlockScaling

namespace Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false

theorem repeated_blocks_length (blocks : List Block) (count : Nat) :
    (((List.replicate count blocks).flatten).map Block.length).sum =
      count * (blocks.map Block.length).sum := by
  induction count with
  | zero => simp only [List.replicate_zero, List.flatten_nil, List.map_nil, List.sum_nil, Nat.zero_mul]
  | succ count ih =>
    rw [List.replicate_succ, List.flatten_cons, List.map_append, List.sum_append, ih, Nat.succ_mul]
    omega

/-- Select a row from a repeated block cycle without expanding its copies. -/
theorem getFromBlocks_repeated (blocks : List Block) (count index : Nat)
    (bound : index < count * (blocks.map Block.length).sum) :
    getFromBlocks (List.replicate count blocks).flatten index =
      getFromBlocks blocks (index % (blocks.map Block.length).sum) := by
  induction count generalizing index with
  | zero => simp only [Nat.zero_mul] at bound; omega
  | succ count ih =>
    rw [List.replicate_succ, List.flatten_cons]
    by_cases inside : index < (blocks.map Block.length).sum
    · rw [getFromBlocks_append_left _ _ _ inside, Nat.mod_eq_of_lt inside]
    · have shifted : index = (blocks.map Block.length).sum +
          (index - (blocks.map Block.length).sum) := by omega
      have remaining : index - (blocks.map Block.length).sum < count * (blocks.map Block.length).sum := by
        rw [Nat.succ_mul] at bound
        omega
      conv_lhs => rw [shifted, skip_blocks]
      rw [ih _ remaining, ← Nat.mod_eq_sub_mod (by omega)]

/-- Short row checks prove the full repeated source interval. -/
theorem checked_cycle_rows (expected : Nat → Nat) (front cycle tail rest : List Block)
    (count period index : Nat)
    (cycleLength : (cycle.map Block.length).sum = period)
    (frontCheck : checkBlockRows expected 0 front = true)
    (cycleCheck : checkBlockRows expected (front.map Block.length).sum cycle = true)
    (tailCheck : checkBlockRows expected (front.map Block.length).sum tail = true)
    (periodic : ∀ a b, a % period = b % period → expected a = expected b)
    (bound : index < (front.map Block.length).sum + count * period + (tail.map Block.length).sum) :
    getFromBlocks (front ++ (List.replicate count cycle).flatten ++ (tail ++ rest)) index =
      some (expected index) := by
  let first := (front.map Block.length).sum
  by_cases inFront : index < first
  · rw [List.append_assoc, getFromBlocks_append_left _ _ _ inFront]
    simpa only [Nat.zero_add] using checkBlockRows_sound expected front 0 index frontCheck inFront
  · have lower : first ≤ index := by omega
    have shifted : index = first + (index - first) := by omega
    rw [List.append_assoc]
    conv_lhs => rw [shifted, skip_blocks]
    by_cases inCycle : index - first < count * period
    · have cycleBound : index - first < count * (cycle.map Block.length).sum := by
        simpa only [cycleLength] using inCycle
      rw [getFromBlocks_append_left _ _ _ (by
        rw [repeated_blocks_length, cycleLength]; exact inCycle), getFromBlocks_repeated _ _ _ cycleBound]
      have positive : 0 < period := by nlinarith
      have value := checkBlockRows_sound expected cycle first ((index - first) % period) cycleCheck
        (by rw [cycleLength]; exact Nat.mod_lt _ positive)
      rw [cycleLength] at ⊢
      have residue : (first + (index - first) % period) % period = index % period := by
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, ← shifted]
      exact value.trans (congrArg some (periodic _ _ residue))
    · have cycleSize : (((List.replicate count cycle).flatten).map Block.length).sum = count * period := by
        rw [repeated_blocks_length, cycleLength]
      have afterCycle : index - first = count * period + (index - first - count * period) := by omega
      conv_lhs => rw [afterCycle, ← cycleSize, skip_blocks]
      rw [cycleSize]
      have inTail : index - first - count * period < (tail.map Block.length).sum := by omega
      rw [getFromBlocks_append_left _ _ _ inTail]
      have value := checkBlockRows_sound expected tail first (index - first - count * period) tailCheck inTail
      have residue : (first + (index - first - count * period)) % period = index % period := by
        have position : index = (first + (index - first - count * period)) + count * period := by omega
        conv_rhs => rw [position, Nat.add_mul_mod_self_right]
      exact value.trans (congrArg some (periodic _ _ residue))

end Airbender.Setup.Proofs
