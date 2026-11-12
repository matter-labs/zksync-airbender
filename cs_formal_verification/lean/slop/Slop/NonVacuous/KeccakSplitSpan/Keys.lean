module
public import Slop.NonVacuous.KeccakSplitSpan.Schedule

@[expose] public section

/-! The keys of call `k` are its round's map applied to the logical keys of its position, and the map is injective:
    so the calls' keys are distinct and inside the span's 62 keys, and the last call that touched one of call `k`'s
    keys is read off the fifteen positions of a round (`logical_touch`, by evaluation over positions). -/

namespace Airbender.NonVacuous.KeccakSplitSpan
open Keccak.Split Keccak.Split.SetupProofs

theorem piSource_injective : ∀ a b : Fin 25, Call.piSource a = Call.piSource b → a = b := by decide

theorem physicalSlot_injective (r : Nat) {a b : Fin 25} (same : Call.physicalSlot r a = Call.physicalSlot r b) :
    a = b := by
  induction r generalizing a b with
  | zero => exact same
  | succ r ih => exact piSource_injective a b (ih same)

theorem roundSlot_lt (r : Nat) {s : Nat} (lane : s < 25) : roundSlot r s < 25 := by
  unfold roundSlot
  simp only [lane, ↓reduceDIte]
  exact Fin.isLt _

theorem roundSlot_injective (r : Nat) {a b : Nat} (same : roundSlot r a = roundSlot r b) : a = b := by
  by_cases ha : a < 25
  · by_cases hb : b < 25
    · unfold roundSlot at same
      simp only [ha, hb, ↓reduceDIte] at same
      exact congrArg Fin.val (physicalSlot_injective r (Fin.ext same))
    · have := roundSlot_lt r ha
      have parked : roundSlot r b = b := by unfold roundSlot; simp only [hb, ↓reduceDIte]
      omega
  · have parked : roundSlot r a = a := by unfold roundSlot; simp only [ha, ↓reduceDIte]
    by_cases hb : b < 25
    · have := roundSlot_lt r hb
      omega
    · unfold roundSlot at same
      simp only [ha, hb, ↓reduceDIte] at same
      exact same

theorem roundKey_injective (r : Nat) {a b : Nat} (same : roundKey r a = roundKey r b) : a = b := by
  unfold roundKey at same
  split_ifs at same with ha hb hb
  · exact same
  · omega
  · omega
  · have := roundSlot_injective r (a := (a - 2) / 2) (b := (b - 2) / 2) (by omega)
    omega

theorem portKey_eq (k j : Nat) : portKey k j = roundKey (k / 15) (logicalKey (k % 15) j) := by
  unfold portKey logicalKey roundKey
  split_ifs <;> try first | rfl | omega
  rw [slotNat_eq, show (2 + 2 * logicalSlot (k % 15) ((j - 2) / 2) + (j - 2) % 2 - 2) / 2 =
    logicalSlot (k % 15) ((j - 2) / 2) by omega]
  omega

theorem portKeys_eq (k : Nat) : portKeys k = (logicalKeys (k % 15)).map (roundKey (k / 15)) := by
  unfold portKeys logicalKeys
  rw [portCount_eq, List.map_map]
  exact List.map_congr_left fun j _ => portKey_eq k j

/-- The keys of a round's position: distinct, and each a register or a half of a slot below 30. -/
theorem logical_keys : ∀ c < 15, (logicalKeys c).Nodup ∧ ∀ key ∈ logicalKeys c, key < 62 := by decide

theorem roundKey_lt (r : Nat) {key : Nat} (small : key < 62) : roundKey r key < 62 := by
  unfold roundKey
  split_ifs
  · exact small
  · by_cases lane : (key - 2) / 2 < 25
    · have := roundSlot_lt r lane
      omega
    · have parked : roundSlot r ((key - 2) / 2) = (key - 2) / 2 := by
        unfold roundSlot; simp only [lane, ↓reduceDIte]
      omega

theorem portKeys_nodup (k : Nat) : (portKeys k).Nodup := by
  rw [portKeys_eq]
  exact (logical_keys _ (Nat.mod_lt _ (by decide))).1.map (fun _ _ same => roundKey_injective _ same)

theorem portKeys_lt {k key : Nat} (member : key ∈ portKeys k) : key < 62 := by
  rw [portKeys_eq] at member
  obtain ⟨logical, present, rfl⟩ := List.mem_map.mp member
  exact roundKey_lt _ ((logical_keys _ (Nat.mod_lt _ (by decide))).2 _ present)

/-- How many calls before a theta+rho or chi call (at position `c`) its port `j`'s key was last touched: x10 and
    x11 one, theta+rho lanes five, `C[x-1]` and `C[x+1]` by column, chi group `g` `5 + y - g`. -/
def distance (c j : Nat) : Nat :=
  if j < 2 then 1
  else if c < 10 then
    (if j < 12 then 5 else if j < 14 then [1, 6, 2, 2, 2].getD (c % 5) 0 else [4, 4, 4, 3, 3].getD (c % 5) 0)
  else 5 + c % 5 - (j - 2) / 2

/-- Port `j` of the call at position `c` reads its key from the call `distance` positions before, and no call in
    between touches it. -/
def touchOk (c j : Nat) : Bool :=
  0 < distance c j && distance c j ≤ c && (logicalKeys (c - distance c j)).contains (logicalKey c j) &&
    (List.range c).all fun i => !decide (c - distance c j < i) || !(logicalKeys i).contains (logicalKey c j)

theorem touch_ok : ∀ c < 15, 5 ≤ c → ∀ j < logicalCount c, touchOk c j = true := by decide

/-- Within a round, port `j` of a theta+rho or chi call reads its key from the call `distance` positions before. -/
theorem logical_touch {c j : Nat} (position : c < 15) (late : 5 ≤ c) (port : j < logicalCount c) :
    0 < distance c j ∧ distance c j ≤ c ∧ logicalKey c j ∈ logicalKeys (c - distance c j) ∧
      ∀ i < c, c - distance c j < i → logicalKey c j ∉ logicalKeys i := by
  have ok := touch_ok c position late j port
  simp only [touchOk, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem, List.all_eq_true,
    List.mem_range, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at ok
  obtain ⟨⟨⟨positive, le⟩, hit⟩, miss⟩ := ok
  refine ⟨positive, le, hit, fun i below after member => ?_⟩
  rcases miss i below with before | absent
  · exact before after
  · have present := List.contains_iff_mem.mpr member
    rw [absent] at present
    exact Bool.false_ne_true present

/-- The last touch of a key `d` calls back, when no call in between touched it. -/
theorem lastTouch_of {key : Nat} : ∀ {k d : Nat}, 0 < d → d ≤ k → key ∈ portKeys (k - d) →
    (∀ i < k, k - d < i → key ∉ portKeys i) → lastTouch k key = some (k - d)
  | 0, _, positive, le, _, _ => by omega
  | k + 1, d, positive, le, hit, miss => by
    unfold lastTouch
    by_cases one : d = 1
    · subst one
      simp only [Nat.add_sub_cancel] at hit
      simp only [hit, ↓reduceIte, Nat.add_sub_cancel]
    · have absent : key ∉ portKeys k := miss k (by omega) (by omega)
      have earlier := lastTouch_of (k := k) (d := d - 1) (by omega) (by omega)
        (by rw [show k - (d - 1) = k + 1 - d by omega]; exact hit)
        (fun i below after => miss i (by omega) (by omega))
      simp only [absent, ↓reduceIte, earlier]
      congr 1
      omega

/-- Port `j` of theta+rho or chi call `k` reads its key from call `k - distance`. -/
theorem touch {k j : Nat} (call : k < 361) (late : 5 ≤ k % 15) (port : j < portCount k) :
    lastTouch k (portKey k j) = some (k - distance (k % 15) j) := by
  rw [portCount_eq] at port
  obtain ⟨positive, le, hit, miss⟩ := logical_touch (Nat.mod_lt _ (by decide)) late port
  have round (i : Nat) (le : i ≤ k % 15) : (k - i) / 15 = k / 15 ∧ (k - i) % 15 = k % 15 - i := by omega
  refine lastTouch_of positive (by omega) ?_ fun i below after => ?_
  · rw [portKeys_eq, (round _ le).1, (round _ le).2, portKey_eq]
    exact List.mem_map_of_mem hit
  · obtain ⟨same, position⟩ := round (k - i) (by omega)
    rw [show k - (k - i) = i by omega] at same position
    rw [portKeys_eq, same, position, portKey_eq]
    intro member
    obtain ⟨other, present, equal⟩ := List.mem_map.mp member
    rw [roundKey_injective _ equal] at present
    exact miss (k % 15 - (k - i)) (by omega) (by omega) present

end Airbender.NonVacuous.KeccakSplitSpan
