module
public import Proven.NonVacuous.DynamicCopyLoop.Boot
public import Proven.NonVacuous.DynamicCopyLoop.FiniteMemory
public import Proven.Trace.PaddingBoundary
public import Proven.Trace.RVBootSeed

@[expose] public section
namespace Airbender.NonVacuous.DynamicCopyLoop
open Trace Arithmetic
set_option warningAsError true

/-- One logical RAM cell in the two public initialization windows. -/
def windowCell (top row : Nat) : Cell :=
  .ram (BitVec.ofNat 32 (InitsTeardowns.windowAddress InitsTeardowns.unifiedLayout top row))

/-- Each inline initialization set has the imported native row count. -/
theorem rows_count : 2 ^ InitsTeardowns.unifiedLayout.traceLog = 8388608 := rfl

/-- Untouched cells comprise window zero and the suffix of window one after both buffers. -/
noncomputable def backgroundCells : List Cell :=
  (List.range 8388608).map (windowCell 0) ++
    (List.range (8388608 - 16)).map (fun offset => windowCell 1 (16 + offset))

/-- A symbolic row range splits at the end of the two finite buffers. -/
theorem range_prefix {α : Type} (length : Nat) (enough : 16 ≤ length) (value : Nat → α) :
    (List.range length).map value = (List.range 16).map value ++
      (List.range (length - 16)).map (fun offset => value (16 + offset)) := by
  have split : length = 16 + (length - 16) := by omega
  conv => lhs; rw [split, List.range_add, List.map_append, List.map_map]
  rfl

/-- The finite domain contains every register and the first sixteen rows of window one. -/
theorem finite_cells : finiteCells = registerCells ++ (List.range 16).map (windowCell 1) := by
  kernel_rfl

/-- The full tracked domain contains both complete inline windows. -/
theorem cells_layout : cells = registerCells ++
    ((List.range 8388608).map (windowCell 0) ++ (List.range 8388608).map (windowCell 1)) := by
  change registerCells ++ InitsTeardowns.windowCells InitsTeardowns.unifiedLayout [0, 1] = _
  simp only [InitsTeardowns.windowCells, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rfl

/-- Every full-domain cell is in the finite transfer domain or the untouched background, with multiplicity. -/
theorem cells_partition : cells.Perm (finiteCells ++ backgroundCells) := by
  simp only [cells_layout, finite_cells, range_prefix 8388608 (by decide) (windowCell 1), backgroundCells]
  simpa only [List.append_assoc] using
    ((List.perm_append_comm (l₁ := (List.range 8388608).map (windowCell 0))
      (l₂ := (List.range 16).map (windowCell 1))).append_right
        ((List.range (8388608 - 16)).map fun offset => windowCell 1 (16 + offset))).append_left registerCells

/-- Window addresses retain their natural-number value without 32-bit truncation. -/
theorem window_address_value (top : Fin 2) (row : Nat) (bounded : row < 8388608) :
    (BitVec.ofNat 32 (InitsTeardowns.windowAddress InitsTeardowns.unifiedLayout top.val row)).toNat =
      top.val * 33554432 + row * 4 := by
  have small := InitsTeardowns.Proofs.window_lt
    (show InitsTeardowns.Proofs.Shape InitsTeardowns.unifiedLayout from ⟨rfl, Or.inl rfl⟩)
    (show top.val < InitsTeardowns.maxTopBit by have h := top.isLt; change _ < 64; omega)
    bounded
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
  rfl

/-- Window zero contains no word in either transfer buffer. -/
theorem window_zero_unchanged (row : Nat) (bounded : row < 8388608) :
    final (windowCell 0 row) = old (windowCell 0 row) := by
  have address := window_address_value 0 row bounded
  have small : row * 4 < 33554432 := Nat.mul_lt_mul_of_pos_right bounded (by decide)
  have outside : ¬(33554432 ≤ (BitVec.ofNat 32
      (InitsTeardowns.windowAddress InitsTeardowns.unifiedLayout 0 row)).toNat ∧
      (BitVec.ofNat 32 (InitsTeardowns.windowAddress InitsTeardowns.unifiedLayout 0 row)).toNat < 33554496) := by
    simp only [Fin.val_zero, Nat.zero_mul, Nat.zero_add] at address
    exact fun both => Nat.not_le.mpr small (address ▸ both.1)
  simp only [windowCell, final]
  rw [ite_eq_right (by simpa only [Bool.and_eq_true, decide_eq_true_eq] using outside)]

/-- The suffix of window one begins after both transfer buffers. -/
theorem window_tail_unchanged (offset : Nat) (bounded : offset < 8388608 - 16) :
    final (windowCell 1 (16 + offset)) = old (windowCell 1 (16 + offset)) := by
  have rowBound : 16 + offset < 8388608 := Nat.add_lt_add_left bounded 16
  have address := window_address_value 1 (16 + offset) rowBound
  have lower : 33554496 ≤ 33554432 + (16 + offset) * 4 :=
    Nat.add_le_add_left (Nat.mul_le_mul_right 4 (Nat.le_add_right 16 offset)) 33554432
  have outside : ¬(33554432 ≤ (BitVec.ofNat 32
      (InitsTeardowns.windowAddress InitsTeardowns.unifiedLayout 1 (16 + offset))).toNat ∧
      (BitVec.ofNat 32 (InitsTeardowns.windowAddress InitsTeardowns.unifiedLayout 1 (16 + offset))).toNat < 33554496) := by
    simp only [Fin.val_one, Nat.one_mul] at address
    exact fun both => Nat.not_lt.mpr lower (address ▸ both.2)
  simp only [windowCell, final]
  rw [ite_eq_right (by simpa only [Bool.and_eq_true, decide_eq_true_eq] using outside)]

/-- Every background cell retains its zero seed token. -/
theorem background_unchanged (cell : Cell) (member : cell ∈ backgroundCells) : final cell = old cell := by
  rcases (List.mem_append
    (s := (List.range 8388608).map (windowCell 0))
    (t := (List.range (8388608 - 16)).map fun offset => windowCell 1 (16 + offset))).mp member with first | last
  · obtain ⟨row, included, same⟩ := (List.mem_map
      (f := windowCell 0) (l := List.range 8388608)).mp first
    exact same ▸ window_zero_unchanged row (List.mem_range.mp included)
  · obtain ⟨offset, included, same⟩ := (List.mem_map
      (f := fun offset => windowCell 1 (16 + offset)) (l := List.range (8388608 - 16))).mp last
    exact same ▸ window_tail_unchanged offset (List.mem_range.mp included)

/-- The logical teardown columns produce the final token of each complete initialization row. -/
theorem teardown_row (set : Fin 2) (row : Nat) (bounded : row < 8388608) :
    InitsTeardowns.teardownToken InitsTeardowns.unifiedLayout InitsTeardowns.unifiedLayout.sets[set]
      set.val row (teardownAssignment row) = final (windowCell set.val row) := by
  fin_cases set
  · have unchanged := window_zero_unchanged row bounded
    rw [unchanged]
    change (⟨InitsTeardowns.addressCode InitsTeardowns.unifiedLayout 0 row,
      (teardownAssignment row 128, teardownAssignment row 129),
      Nat.pair (teardownAssignment row 126).val (teardownAssignment row 127).val⟩ : MemoryToken babyBearModulus) = _
    rw [InitsTeardowns.Proofs.addressCode_eq ⟨rfl, Or.inl rfl⟩ (by decide) bounded]
    simp only [teardownAssignment, Nat.reduceBEq, Bool.and_false, Bool.false_eq_true,
      ↓reduceIte]
    rfl
  · let address := BitVec.ofNat 32 (InitsTeardowns.windowAddress InitsTeardowns.unifiedLayout 1 row)
    have addressValue : address.toNat = 33554432 + row * 4 := by
      simpa only [Fin.val_one, Nat.one_mul] using window_address_value 1 row bounded
    have first : address = destinationAddress ↔ row = 0 := by
      constructor
      · intro same
        have value := congrArg BitVec.toNat same
        change address.toNat = 33554432 at value
        rw [addressValue] at value
        have products : row * 4 = 0 * 4 := Nat.add_left_cancel
          (show 33554432 + row * 4 = 33554432 + 0 * 4 from value)
        exact Nat.mul_right_cancel (by decide) products
      · rintro rfl
        rfl
    have source : address = sourceAddress ↔ row = 8 := by
      constructor
      · intro same
        have value := congrArg BitVec.toNat same
        change address.toNat = 33554464 at value
        rw [addressValue] at value
        have products : row * 4 = 8 * 4 := Nat.add_left_cancel
          (show 33554432 + row * 4 = 33554432 + 8 * 4 from value)
        exact Nat.mul_right_cancel (by decide) products
      · rintro rfl
        rfl
    have lower : 33554432 ≤ address.toNat := by
      rw [addressValue]
      exact Nat.le_add_right _ _
    have upper : address.toNat < 33554496 ↔ row < 16 := by
      rw [addressValue]
      change (33554432 + row * 4 < 33554432 + 16 * 4) ↔ row < 16
      rw [Nat.add_lt_add_iff_left, Nat.mul_lt_mul_right (by decide)]
    have rangeCondition : (33554432 ≤ address.toNat ∧ address.toNat < 33554496) ↔ row < 16 :=
      ⟨fun both => upper.mp both.2, fun selected => ⟨lower, upper.mpr selected⟩⟩
    change (⟨InitsTeardowns.addressCode InitsTeardowns.unifiedLayout 1 row,
      (teardownAssignment row 132, teardownAssignment row 133),
      Nat.pair (teardownAssignment row 130).val (teardownAssignment row 131).val⟩ : MemoryToken babyBearModulus) = _
    rw [InitsTeardowns.Proofs.addressCode_eq ⟨rfl, Or.inl rfl⟩ (by decide) bounded]
    simp only [windowCell, final, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
    change _ = if 33554432 ≤ address.toNat ∧ address.toNat < 33554496 then
      (⟨(Cell.ram address).addressCode, (51, 0),
        Nat.pair (if address = destinationAddress ∨ address = sourceAddress then 7 else 0) 0⟩ : MemoryToken babyBearModulus)
      else old (Cell.ram address)
    simp only [rangeCondition, first, source]
    by_cases active : row < 16
    · by_cases special : row = 0 ∨ row = 8
      · simp [teardownAssignment, active, special, address]
        rfl
      · simp [teardownAssignment, active, special, address]
    · have notZero : row ≠ 0 := by rintro rfl; exact active (by decide)
      have notEight : row ≠ 8 := by rintro rfl; exact active (by decide)
      simp [teardownAssignment, active, notZero, notEight, old, Cell.initialToken, Word.ofBitVec, address]

/-- The complete public seed list is the zero image of the full tracked domain. -/
theorem initial_image : trace.initialMemory = cells.map old := by
  change trace.initialMemory = ROMView.nativeBootImage cells
  exact Trace.Proofs.boot_seed_image (InitsTeardowns.Proofs.claims ⟨rfl, Or.inl rfl⟩)
    checked boot.seeds boot.domain

/-- Inline teardown lists retain the native set order and every row of both windows. -/
theorem teardown_shape : inits.flatMap InitsTeardowns.Witness.teardownTokens =
    (List.range 8388608).map (fun row => InitsTeardowns.teardownToken InitsTeardowns.unifiedLayout
      InitsTeardowns.unifiedLayout.sets[0] 0 row (teardownAssignment row)) ++
    (List.range 8388608).map (fun row => InitsTeardowns.teardownToken InitsTeardowns.unifiedLayout
      InitsTeardowns.unifiedLayout.sets[1] 1 row (teardownAssignment row)) := by
  let witness : InitsTeardowns.Witness babyBearModulus InitsTeardowns.unifiedLayout :=
    ⟨#v[0, 1], teardownAssignment⟩
  have outer : inits.flatMap InitsTeardowns.Witness.teardownTokens = witness.teardownTokens := by
    change [witness].flatMap InitsTeardowns.Witness.teardownTokens = _
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have zipped : (witness.topBits.toList.zip InitsTeardowns.unifiedLayout.sets.toList) =
      [(0, InitsTeardowns.unifiedLayout.sets[0]), (1, InitsTeardowns.unifiedLayout.sets[1])] := rfl
  rw [outer]
  change (witness.topBits.toList.zip InitsTeardowns.unifiedLayout.sets.toList).flatMap
    (fun pair => (InitsTeardowns.rows InitsTeardowns.unifiedLayout).map fun row =>
      InitsTeardowns.teardownToken InitsTeardowns.unifiedLayout pair.2 pair.1 row (witness.assignment row)) = _
  rw [zipped]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, InitsTeardowns.rows, rows_count]
  rfl

/-- Native teardown tokens give the final image of all initialized RAM cells. -/
theorem ram_terminal_image : inits.flatMap InitsTeardowns.Witness.teardownTokens =
    (InitsTeardowns.windowCells InitsTeardowns.unifiedLayout [0, 1]).map final := by
  have left : (List.range 8388608).map (fun row => InitsTeardowns.teardownToken InitsTeardowns.unifiedLayout
      InitsTeardowns.unifiedLayout.sets[0] 0 row (teardownAssignment row)) =
      (List.range 8388608).map (fun row => final (windowCell 0 row)) := by
    apply List.map_congr_left
    intro row member
    have bounded := List.mem_range.mp member
    clear member
    exact teardown_row 0 row bounded
  have right : (List.range 8388608).map (fun row => InitsTeardowns.teardownToken InitsTeardowns.unifiedLayout
      InitsTeardowns.unifiedLayout.sets[1] 1 row (teardownAssignment row)) =
      (List.range 8388608).map (fun row => final (windowCell 1 row)) := by
    apply List.map_congr_left
    intro row member
    have bounded := List.mem_range.mp member
    clear member
    exact teardown_row 1 row bounded
  simp only [teardown_shape, left, right, InitsTeardowns.windowCells, InitsTeardowns.rows, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.map_append, List.map_map, Function.comp_def, windowCell, rows_count]

/-- All terminal register and RAM values form the final image of the full tracked domain. -/
theorem terminal_image : trace.terminalMemory = cells.map final := by
  change registerCells.map final ++ inits.flatMap InitsTeardowns.Witness.teardownTokens =
    (registerCells ++ InitsTeardowns.windowCells InitsTeardowns.unifiedLayout [0, 1]).map final
  simpa only [List.map_append] using congrArg (registerCells.map final ++ ·) ram_terminal_image

/-- The framed trace retains every actual CPU and worker transfer of the finite trace. -/
theorem steps_eq : Trace.Machine.unifiedSteps trace ++ workers.steps = steps := by
  have rows : trace.rows = finiteTrace.rows := rfl
  unfold steps Trace.Machine.unifiedSteps
  rw [rows]

/-- Full-domain matching adds each untouched zero token to both sides of the finite transfer permutation. -/
theorem memory_matching :
    (trace.initialMemory ++ (Trace.Machine.unifiedSteps trace ++ workers.steps).map Prod.snd).Perm
      (trace.terminalMemory ++ (Trace.Machine.unifiedSteps trace ++ workers.steps).map Prod.fst) := by
  let background := backgroundCells.map old
  have first : trace.initialMemory.Perm (finiteTrace.initialMemory ++ background) := by
    rw [initial_image]
    simpa only [finiteTrace, List.map_append] using cells_partition.map old
  have last : trace.terminalMemory.Perm (finiteTrace.terminalMemory ++ background) := by
    rw [terminal_image]
    have same : backgroundCells.map final = backgroundCells.map old := by
      apply List.map_congr_left
      exact background_unchanged
    simpa only [finiteTrace, List.map_append, same] using cells_partition.map final
  have framed : ((finiteTrace.initialMemory ++ background) ++ steps.map Prod.snd).Perm
      ((finiteTrace.terminalMemory ++ background) ++ steps.map Prod.fst) := by
    simpa only [List.append_assoc] using
      PaddingBoundary.Proofs.insert_identities finite_memory_matching background
  rw [steps_eq]
  exact (first.append_right _).trans (framed.trans (last.symm.append_right _))

end Airbender.NonVacuous.DynamicCopyLoop
