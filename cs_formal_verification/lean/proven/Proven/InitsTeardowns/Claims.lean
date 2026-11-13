module
public import Proven.InitsTeardowns.Window

@[expose] public section

/-! The `Claims` of `Human.Circuits.InitsTeardowns.Theorems` for any layout of `Shape`. -/

namespace Airbender.InitsTeardowns.Proofs
open Trace Arithmetic

theorem flatMap_congr_mem {α β : Type} {l : List α} {f g : α → List β} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    rw [h x (by simp), ih fun y hy => h y (by simp [hy])]

/-- Window addresses determine top bits and row. -/
theorem window_injective {layout : Layout} (shape : Shape layout) {a b r s : Nat} (ha : a < maxTopBit)
    (hb : b < maxTopBit) (hr : r < 2 ^ layout.traceLog) (hs : s < 2 ^ layout.traceLog)
    (h : BitVec.ofNat 32 (windowAddress layout a r) = BitVec.ofNat 32 (windowAddress layout b s)) :
    a = b ∧ r = s := by
  have h := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (window_lt shape ha hr),
    Nat.mod_eq_of_lt (window_lt shape hb hs)] at h
  obtain ⟨hw, hT⟩ := shape
  unfold windowAddress maxTopBit at *
  rw [hw] at h
  rcases hT with hT | hT <;> rw [hT] at h hr hs <;> norm_num at h hr hs <;> omega

theorem init_claim {layout : Layout} (shape : Shape layout) {top row : Nat} (htop : top < maxTopBit)
    (hrow : row < 2 ^ layout.traceLog) :
    initToken (p := babyBearModulus) layout top row =
      (Cell.ram (BitVec.ofNat 32 (windowAddress layout top row))).initialToken 0 := by
  simp only [initToken, Cell.initialToken, addressCode_eq shape htop hrow]
  rfl

theorem windowCells_nodup {layout : Layout} (shape : Shape layout) {topBits : List Nat}
    (checked : TopBitsChecked topBits) : (windowCells layout topBits).Nodup := by
  obtain ⟨increasing, bounded⟩ := checked
  unfold windowCells
  rw [List.nodup_flatMap]
  refine ⟨fun top htop => ?_, ?_⟩
  · refine (List.nodup_range).map_on fun r hr s hs h => ?_
    simp only [rows, List.mem_range] at hr hs
    exact (window_injective shape (bounded top htop) (bounded top htop) hr hs (Cell.ram.inj h)).2
  · refine increasing.imp_of_mem fun {a b} ha hb hab => ?_
    intro cell hcell hcell'
    simp only [rows, List.mem_map, List.mem_range] at hcell hcell'
    obtain ⟨r, hr, rfl⟩ := hcell
    obtain ⟨s, hs, h⟩ := hcell'
    have := (window_injective shape (bounded b hb) (bounded a ha) hs hr (Cell.ram.inj h)).1
    omega

theorem initTokens_eq {layout : Layout} (shape : Shape layout) {topBits : List Nat}
    (bounded : ∀ top ∈ topBits, top < maxTopBit) :
    initTokens (p := babyBearModulus) layout topBits = ROMView.nativeBootImage (windowCells layout topBits) := by
  unfold initTokens ROMView.nativeBootImage windowCells
  rw [List.map_flatMap]
  refine flatMap_congr_mem fun top htop => ?_
  rw [List.map_map]
  refine List.map_congr_left fun row hrow => ?_
  simp only [rows, List.mem_range] at hrow
  exact init_claim shape (bounded top htop) hrow

theorem boot_image {layout : Layout} (shape : Shape layout) (instances : List (Witness babyBearModulus layout))
    (checked : TopBitsChecked (instances.flatMap fun w => w.topBits.toList)) :
    (windowCells layout (instances.flatMap fun w => w.topBits.toList)).Nodup ∧
    instances.flatMap Witness.initTokens =
      ROMView.nativeBootImage (windowCells layout (instances.flatMap fun w => w.topBits.toList)) := by
  refine ⟨windowCells_nodup shape checked, ?_⟩
  rw [← initTokens_eq shape checked.2]
  unfold Witness.initTokens initTokens
  rw [List.flatMap_assoc]

theorem teardown_addresses {layout : Layout} (w : Witness babyBearModulus layout) :
    w.teardownTokens.map MemoryToken.address = w.initTokens.map MemoryToken.address := by
  unfold Witness.teardownTokens Witness.initTokens initTokens
  have hlen : w.topBits.toList.length = layout.sets.toList.length := by simp
  rw [List.map_flatMap, List.map_flatMap]
  conv => rhs; rw [← List.map_fst_zip (l₁ := w.topBits.toList) (l₂ := layout.sets.toList) (by omega),
    List.flatMap_map]
  refine flatMap_congr_mem fun _ _ => ?_
  simp only [List.map_map]
  rfl

theorem teardown_mem {layout : Layout} (w : Witness babyBearModulus layout) {s : Nat}
    (hs : s < layout.sets.size) {row : Nat} (hrow : row < 2 ^ layout.traceLog) :
    teardownToken layout layout.sets[s] w.topBits[s] row (w.assignment row) ∈ w.teardownTokens := by
  unfold Witness.teardownTokens
  rw [List.mem_flatMap]
  refine ⟨(w.topBits[s], layout.sets[s]), ?_, ?_⟩
  · have hz : s < (w.topBits.toList.zip layout.sets.toList).length := by simp [hs]
    have := List.getElem_mem hz
    simpa using this
  · exact List.mem_map.2 ⟨row, by simpa [rows] using hrow, rfl⟩

theorem claims {layout : Layout} (shape : Shape layout) : Claims layout where
  init := fun top htop row hrow =>
    ⟨window_lt shape htop hrow, window_aligned shape htop hrow, init_claim shape htop hrow, rfl, rfl⟩
  bootImage := boot_image shape
  teardown := fun w => ⟨teardown_addresses w, fun s hs row hrow =>
    ⟨teardown_mem w hs hrow, fun htop => by
      simp only [teardownToken, addressCode_eq shape htop hrow]⟩⟩
  checkable := ⟨List.pairwise_lt_range, fun _ h => List.mem_range.1 h⟩

/-- Every aligned word below `maxTopBit` windows lies in the windows of `0, …, maxTopBit - 1`. -/
theorem covered {layout : Layout} (shape : Shape layout) (address : BitVec 32)
    (aligned : (Cell.ram address).Aligned)
    (below : address.toNat < maxTopBit * 2 ^ (layout.traceLog + layout.wordBits)) :
    Cell.ram address ∈ windowCells layout (List.range maxTopBit) := by
  obtain ⟨hw, hT⟩ := shape
  simp only [Cell.Aligned] at aligned
  unfold windowCells
  rw [List.mem_flatMap]
  refine ⟨address.toNat / 2 ^ (layout.traceLog + layout.wordBits), ?_,
    List.mem_map.2 ⟨address.toNat % 2 ^ (layout.traceLog + layout.wordBits) / 2 ^ layout.wordBits, ?_, ?_⟩⟩
  · rw [List.mem_range]
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact below)
  · simp only [rows, List.mem_range]
    rw [hw]
    rcases hT with hT | hT <;> rw [hT] <;> norm_num <;> omega
  · congr 1
    apply BitVec.eq_of_toNat_eq
    have := address.isLt
    unfold windowAddress
    rw [BitVec.toNat_ofNat, hw]
    rcases hT with hT | hT <;> rw [hT] <;> norm_num <;> omega

end Airbender.InitsTeardowns.Proofs
