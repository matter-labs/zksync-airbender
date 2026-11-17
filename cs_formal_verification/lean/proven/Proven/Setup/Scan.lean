module
public import Proven.Setup.Blocks

@[expose] public section

/- Kernel check of an imported setup column against a row formula `spec`. The kernel evaluates `scan`
   (`decide +kernel`): it checks each short block row by row, and each long block on one period (the anchor period)
   and on the rows outside its covered periods. A separate algebraic proof (`Long.Ok`) states that the formula
   repeats with the period and the stride of that long block. The checks use only recursors and primitive
   operations, and the loops compute each row from the recursion index, so that each row costs few kernel steps and
   no term grows with the row count. One column is split into slices of consecutive blocks (`SliceOk`), one kernel
   check each; `PrefixOk` joins them. -/

namespace Airbender.Import.Setup.Scan

open Airbender.Import.Setup Airbender.Import.Setup.Proofs

noncomputable section

/-- `yes` when `condition` holds, else `no`: one kernel step, for the column formulas. -/
def pick {α : Sort _} (condition : Bool) (yes no : α) : α := Bool.rec no yes condition

theorem pick_decide {α : Sort _} (p : Prop) [Decidable p] (yes no : α) :
    pick (decide p) yes no = if p then yes else no := by
  by_cases h : p <;> simp [pick, h]

/-! `pick_of_true` and `pick_of_false` are not proved by `rfl`: `simp` then rewrites with them instead of by unfolding
`pick`, and the kernel does not compare the two sides by unfolding the selected value (slow on row formulas). -/

@[simp] theorem pick_of_true {α : Sort _} (yes no : α) : pick true yes no = yes := Eq.trans rfl rfl

@[simp] theorem pick_of_false {α : Sort _} (yes no : α) : pick false yes no = no := Eq.trans rfl rfl

theorem pick_true {α : Sort _} {p : Prop} [Decidable p] {yes no : α} (h : p) : pick (decide p) yes no = yes := by
  simp [pick, h]

theorem pick_false {α : Sort _} {p : Prop} [Decidable p] {yes no : α} (h : ¬p) : pick (decide p) yes no = no := by
  simp [pick, h]

/-- Both checks hold. The kernel evaluates `second` only when `first` holds. -/
def both (first second : Bool) : Bool := Bool.rec false second first

theorem both_eq_true {first second : Bool} (h : both first second = true) : first = true ∧ second = true := by
  cases first <;> simp_all [both]

/-- `value + offset` is the natural number `expected`. A negative `value` fails: the native values are canonical. -/
def isShifted (value offset : Int) (expected : Nat) : Bool :=
  Int.casesOn (motive := fun _ => Bool) value
    (fun natural => Int.casesOn (motive := fun _ => Bool) offset
      (fun shift => Nat.beq (Nat.add natural shift) expected)
      (fun shift => Nat.beq natural (Nat.add expected (Nat.succ shift))))
    (fun _ => false)

theorem isShifted_eq {value offset : Int} {expected : Nat} (h : isShifted value offset expected = true) :
    value + offset = expected := by
  cases value with
  | ofNat natural =>
    cases offset with
    | ofNat shift =>
      have sum : natural + shift = expected := Nat.eq_of_beq_eq_true h
      simp only [Int.ofNat_eq_natCast]
      omega
    | negSucc shift =>
      have sum : natural = expected + (shift + 1) := Nat.eq_of_beq_eq_true h
      simp only [Int.ofNat_eq_natCast, Int.negSucc_eq]
      omega
  | negSucc _ => simp [isShifted] at h

/-- Each `values[j] + offset` is the expected value of row `row + j`. -/
def checkValues (spec : Nat → Nat) (offset : Int) (values : List Int) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun value _ rest row => both (isShifted value offset (spec row)) (rest (Nat.succ row))) values

theorem checkValues_sound {spec : Nat → Nat} {offset : Int} {values : List Int} {row : Nat}
    (h : checkValues spec offset values row = true) :
    ∀ j (hj : j < values.length), values[j] + offset = spec (row + j) := by
  induction values generalizing row with
  | nil => intro j hj; simp at hj
  | cons value values ih =>
    have h := both_eq_true (show both (isShifted value offset (spec row))
      (checkValues spec offset values (row + 1)) = true from h)
    intro j hj
    cases j with
    | zero => simpa using isShifted_eq h.1
    | succ j =>
      have := ih h.2 j (by simpa using hj)
      simpa [Nat.add_assoc, Nat.add_comm 1 j] using this

/-- Row `row + j` holds `value + step * j`, for every `j < count`, with natural `value` and `step`. The row and the
    value come from the recursion index, a literal, so that no term grows with `count`. -/
def checkRun (spec : Nat → Nat) (step count row value : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun j rest => both (Nat.beq (Nat.add value (Nat.mul step j)) (spec (Nat.add row j))) rest) count

theorem checkRun_sound {spec : Nat → Nat} {step count row value : Nat}
    (h : checkRun spec step count row value = true) : ∀ j < count, value + step * j = spec (row + j) := by
  induction count with
  | zero => intro j hj; omega
  | succ count ih =>
    have h := both_eq_true (show both (Nat.beq (value + step * count) (spec (row + count)))
      (checkRun spec step count row value) = true from h)
    intro j hj
    by_cases last : j = count
    · subst last; exact Nat.eq_of_beq_eq_true h.1
    · exact ih h.2 j (by omega)

/-- Row `row + j` holds `value + step * j`, for every `j < count`. -/
def checkSteps (spec : Nat → Nat) (step : Int) (count row : Nat) (value : Int) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun j rest => both (isShifted (Int.add value (Int.mul step (Int.ofNat j))) 0 (spec (Nat.add row j))) rest)
    count

theorem checkSteps_sound {spec : Nat → Nat} {step : Int} {count row : Nat} {value : Int}
    (h : checkSteps spec step count row value = true) :
    ∀ j < count, value + step * j = spec (row + j) := by
  induction count with
  | zero => intro j hj; omega
  | succ count ih =>
    have h := both_eq_true (show both (isShifted (value + step * (count : Int)) 0 (spec (row + count)))
      (checkSteps spec step count row value) = true from h)
    intro j hj
    by_cases last : j = count
    · subst last; simpa using isShifted_eq h.1
    · exact ih h.2 j (by omega)

/-- `first + step * j` is the expected value of row `row + j`, for every `j < count`; natural arithmetic when
    `first` and `step` are natural. -/
def checkAffine (spec : Nat → Nat) (step : Int) (count row : Nat) (first : Int) : Bool :=
  Int.casesOn (motive := fun _ => Bool) first
    (fun value => Int.casesOn (motive := fun _ => Bool) step
      (fun increment => checkRun spec increment count row value)
      (fun _ => checkSteps spec step count row first))
    (fun _ => checkSteps spec step count row first)

theorem checkAffine_sound {spec : Nat → Nat} {step : Int} {count row : Nat} {first : Int}
    (h : checkAffine spec step count row first = true) :
    ∀ j < count, first + step * j = spec (row + j) := by
  cases first with
  | ofNat value =>
    cases step with
    | ofNat increment =>
      intro j hj
      have := checkRun_sound h j hj
      simp only [Int.ofNat_eq_natCast]
      exact_mod_cast this
    | negSucc _ => exact checkSteps_sound h
  | negSucc _ => exact checkSteps_sound h

/-- `reps` repetitions of `values` (of length `period`), the `q`-th from row `row + q * period`, shifted by
    `offset + stride * q`. The row and the shift come from the recursion index, a literal. -/
def checkPeriodic (spec : Nat → Nat) (stride : Int) (values : List Int) (period reps row : Nat) (offset : Int) :
    Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun q rest => both
      (checkValues spec (Int.add offset (Int.mul stride (Int.ofNat q))) values (Nat.add row (Nat.mul q period)))
      rest) reps

theorem checkPeriodic_sound {spec : Nat → Nat} {stride : Int} {values : List Int} {reps row : Nat}
    {offset : Int} (h : checkPeriodic spec stride values values.length reps row offset = true) :
    ∀ q < reps, ∀ j (hj : j < values.length),
      values[j] + (offset + stride * q) = spec (row + q * values.length + j) := by
  induction reps with
  | zero => intro q hq; omega
  | succ reps ih =>
    have h := both_eq_true (show both (checkValues spec (offset + stride * (reps : Int)) values
      (row + reps * values.length)) (checkPeriodic spec stride values values.length reps row offset) = true from h)
    intro q hq j hj
    by_cases last : q = reps
    · subst last; exact checkValues_sound h.1 j hj
    · exact ih h.2 q (by omega) j hj

/-- Row-by-row check of a block that starts at row `row`. -/
def checkBlock (spec : Nat → Nat) (row : Nat) (block : Block) : Bool :=
  Block.casesOn (motive := fun _ => Bool) block
    (fun count first step => checkAffine spec step count row first)
    (fun values => checkValues spec 0 values.toList row)
    (fun reps stride values => checkPeriodic spec stride values.toList values.toList.length reps row 0)
    (fun _ _ => false)

/-- The formula as integers. -/
abbrev asInt (spec : Nat → Nat) (n : Nat) : Int := spec n

private theorem array_getD (values : Array Int) (j : Nat) (hj : j < values.toList.length) :
    values.getD j 0 = values.toList[j] := by
  simp only [Array.length_toList] at hj
  simp [Array.getD, hj]

theorem checkBlock_sound {spec : Nat → Nat} {row : Nat} {block : Block}
    (h : checkBlock spec row block = true) : BlockOk (asInt spec) row block := by
  cases block with
  | affine count first step =>
    intro i hi
    simpa [Block.valueAt] using checkAffine_sound h i hi
  | dense values =>
    intro i hi
    simp only [Block.len] at hi
    have hj : i < values.toList.length := by simpa using hi
    simpa [Block.valueAt, array_getD values i hj] using checkValues_sound h i hj
  | periodic reps stride values =>
    apply periodic_ok
    intro q hq j hj
    simpa using checkPeriodic_sound h q hq j hj
  | grid _ _ => simp [checkBlock] at h

/-! Long blocks. The kernel checks one period row by row: the anchor period. `Long.Ok` gives the next `reps - 1`
periods. The kernel checks the periods before the anchor and after the covered periods row by row: they cover rows
where the formula has no algebraic form, such as controller rows. -/

/-- A long block at row `start`: periods of `period` rows, each shifted by `stride` from the previous. The anchor
    period follows `skip` periods; `Long.Ok` covers `reps` periods from the anchor. -/
structure Long where
  /-- The first row of the block. -/
  start : Nat
  /-- The number of periods before the anchor period. -/
  skip : Nat
  /-- The number of rows of one period. -/
  period : Nat
  /-- The number of periods that `Long.Ok` covers, the anchor included. -/
  reps : Nat
  /-- The difference between the values of two consecutive periods. -/
  stride : Int

/-- The first row of the anchor period. -/
abbrev Long.anchor (long : Long) : Nat := long.start + long.skip * long.period

/-- The formula repeats with the period and the stride of `long`, from the anchor period. -/
def Long.Ok (spec : Nat → Nat) (long : Long) : Prop :=
  ∀ q < long.reps, ∀ j < long.period,
    (spec (long.anchor + q * long.period + j) : Int) = spec (long.anchor + j) + long.stride * q

/-- The block has the period and stride of `long` and room for its periods; the kernel checks the anchor period and
    the periods outside the covered ones row by row. -/
def checkLong (spec : Nat → Nat) (long : Long) (block : Block) : Bool :=
  Block.casesOn (motive := fun _ => Bool) block
    (fun count first step =>
      and (and (Nat.beq long.period 1) (Nat.ble (long.skip + long.reps) count))
        (and (and (decide (long.stride = step)) (checkAffine spec step long.skip long.start first))
          (and (isShifted (first + step * long.skip) 0 (spec long.anchor))
            (checkAffine spec step (count - (long.skip + long.reps)) (long.start + (long.skip + long.reps))
              (first + step * (long.skip + long.reps))))))
    (fun _ => false)
    (fun reps stride values =>
      and (and (Nat.beq long.period values.toList.length) (Nat.ble (long.skip + long.reps) reps))
        (and (and (decide (long.stride = stride))
            (checkPeriodic spec stride values.toList values.toList.length long.skip long.start 0))
          (and (checkValues spec (stride * long.skip) values.toList long.anchor)
            (checkPeriodic spec stride values.toList values.toList.length (reps - (long.skip + long.reps))
              (long.start + (long.skip + long.reps) * values.toList.length) (stride * (long.skip + long.reps))))))
    (fun _ _ => false)

theorem checkLong_sound {spec : Nat → Nat} {long : Long} {block : Block} (ok : long.Ok spec)
    (h : checkLong spec long block = true) : BlockOk (asInt spec) long.start block := by
  cases block with
  | affine count first step =>
    change ((long.period.beq 1 && (long.skip + long.reps).ble count) &&
      ((decide (long.stride = step) && checkAffine spec step long.skip long.start first) &&
        (isShifted (first + step * long.skip) 0 (spec long.anchor) &&
          checkAffine spec step (count - (long.skip + long.reps)) (long.start + (long.skip + long.reps))
            (first + step * (long.skip + long.reps))))) = true at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨period, room⟩, ⟨stride, before⟩, anchor_ok, after⟩ := h
    have period := Nat.eq_of_beq_eq_true period
    have room := Nat.le_of_ble_eq_true room
    have anchor_eq := isShifted_eq anchor_ok
    rw [Int.add_zero] at anchor_eq
    intro i hi
    simp only [Block.len] at hi
    simp only [Block.valueAt, asInt]
    by_cases early : i < long.skip
    · exact checkAffine_sound before i early
    by_cases covered : i < long.skip + long.reps
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt early)
      have := ok k (by omega) 0 (by omega)
      simp only [Long.anchor, period, Nat.mul_one, Nat.add_zero] at this anchor_eq
      rw [← Nat.add_assoc, this, ← anchor_eq, stride]
      push_cast
      ring
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt covered)
      have := checkAffine_sound after k (by omega)
      rw [show long.start + (long.skip + long.reps) + k = long.start + (long.skip + long.reps + k) by omega]
        at this
      rw [← this]
      push_cast
      ring
  | dense values => simp [checkLong] at h
  | periodic reps stride values =>
    change ((long.period.beq values.toList.length && (long.skip + long.reps).ble reps) &&
      ((decide (long.stride = stride) &&
          checkPeriodic spec stride values.toList values.toList.length long.skip long.start 0) &&
        (checkValues spec (stride * long.skip) values.toList long.anchor &&
          checkPeriodic spec stride values.toList values.toList.length (reps - (long.skip + long.reps))
            (long.start + (long.skip + long.reps) * values.toList.length)
            (stride * (long.skip + long.reps))))) = true at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨period, room⟩, ⟨stride_eq, before⟩, anchor_ok, after⟩ := h
    have period := Nat.eq_of_beq_eq_true period
    have room := Nat.le_of_ble_eq_true room
    apply periodic_ok
    intro q hq j hj
    simp only [asInt]
    by_cases early : q < long.skip
    · have := checkPeriodic_sound before q early j hj
      rw [← this]
      ring
    by_cases covered : q < long.skip + long.reps
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt early)
      have anchor_j := checkValues_sound anchor_ok j hj
      have repeat_j := ok k (by omega) j (by omega)
      simp only [Long.anchor, period] at repeat_j anchor_j
      rw [show long.start + (long.skip + k) * values.toList.length + j =
        long.start + long.skip * values.toList.length + k * values.toList.length + j by ring, repeat_j,
        ← anchor_j, stride_eq]
      push_cast
      ring
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt covered)
      have := checkPeriodic_sound after k (by omega) j hj
      rw [show long.start + (long.skip + long.reps) * values.toList.length + k * values.toList.length + j =
        long.start + (long.skip + long.reps + k) * values.toList.length + j by ring] at this
      rw [← this]
      push_cast
      ring
  | grid _ _ => simp [checkLong] at h

/-! The scan of a list of blocks. -/

/-- The blocks, the first at row `row`: a block whose first row starts `longs` is checked as that long block, any
    other block row by row. The result is the row after the last block, or `none` on a mismatch. -/
def scan (spec : Nat → Nat) (blocks : List Block) : List Long → Nat → Option Nat :=
  List.rec (motive := fun _ => List Long → Nat → Option Nat) (fun _ row => some row)
    (fun block _ rest longs row =>
      List.casesOn (motive := fun _ => Option Nat) longs
        (cond (checkBlock spec row block) (rest [] (Nat.add row block.len)) none)
        (fun long others =>
          cond (Nat.beq long.start row)
            (cond (checkLong spec long block) (rest others (Nat.add row block.len)) none)
            (cond (checkBlock spec row block) (rest longs (Nat.add row block.len)) none))) blocks

theorem scan_sound {spec : Nat → Nat} {blocks : List Block} {longs : List Long} {row last : Nat}
    (ok : ∀ long ∈ longs, long.Ok spec) (h : scan spec blocks longs row = some last) :
    Matches (asInt spec) row blocks ∧ row + total blocks = last := by
  induction blocks generalizing longs row with
  | nil =>
    change some row = some last at h
    simp only [Option.some.injEq] at h
    exact ⟨trivial, by simp [total, h]⟩
  | cons block blocks ih =>
    have step : ∀ (check : Bool) (others : List Long),
        (∀ long ∈ others, long.Ok spec) → (check = true → BlockOk (asInt spec) row block) →
        cond check (scan spec blocks others (row + block.len)) none = some last →
        Matches (asInt spec) row (block :: blocks) ∧ row + total (block :: blocks) = last := by
      intro check others others_ok sound h
      cases check with
      | false => simp at h
      | true =>
        obtain ⟨tail, ends⟩ := ih others_ok h
        exact ⟨⟨sound rfl, tail⟩, by simp only [total]; omega⟩
    cases longs with
    | nil => exact step _ [] (by simp) checkBlock_sound h
    | cons long others =>
      change cond (Nat.beq long.start row)
        (cond (checkLong spec long block) (scan spec blocks others (row + block.len)) none)
        (cond (checkBlock spec row block) (scan spec blocks (long :: others) (row + block.len)) none) =
          some last at h
      by_cases same : long.start = row
      · rw [show Nat.beq long.start row = true by simpa using same] at h
        exact step _ others (fun l hl => ok l (List.mem_cons_of_mem _ hl))
          (fun c => same ▸ checkLong_sound (ok long List.mem_cons_self) c) h
      · have differ : Nat.beq long.start row = false := by
          cases test : Nat.beq long.start row
          · rfl
          · exact absurd (Nat.eq_of_beq_eq_true test) same
        rw [differ] at h
        exact step _ (long :: others) ok checkBlock_sound h

/-! Slices of a column, joined in order. -/

/-- The rows before `row` decode to the formula, and `row` is the first row after the first `count` blocks. -/
def PrefixOk (spec : Nat → Nat) (blocks : List Block) (count row : Nat) : Prop :=
  total (blocks.take count) = row ∧ ∀ n < row, decode blocks n = spec n

/-- The `count` blocks from block `first` pass the scan from row `row` to row `last`. -/
abbrev SliceOk (spec : Nat → Nat) (blocks : List Block) (first count : Nat) (longs : List Long)
    (row last : Nat) : Prop :=
  scan spec ((blocks.drop first).take count) longs row = some last

theorem prefixOk_zero (spec : Nat → Nat) (blocks : List Block) : PrefixOk spec blocks 0 0 :=
  ⟨by simp [total], fun n hn => absurd hn (Nat.not_lt_zero n)⟩

theorem total_append (front back : List Block) : total (front ++ back) = total front + total back := by
  induction front with
  | nil => simp [total]
  | cons block front ih => simp only [List.cons_append, total, ih]; omega

theorem decode_append (front back : List Block) (n : Nat) :
    decode (front ++ back) n = if n < total front then decode front n else decode back (n - total front) := by
  induction front generalizing n with
  | nil => simp [total]
  | cons block front ih =>
    simp only [List.cons_append, decode, total]
    by_cases inside : n < block.len
    · simp [inside, show n < block.len + total front by omega]
    · simp only [inside, ↓reduceIte, ih]
      by_cases rest : n - block.len < total front
      · simp [rest, show n < block.len + total front by omega]
      · simp only [rest, ↓reduceIte, show ¬n < block.len + total front by omega]
        congr 1
        omega

theorem prefixOk_step {spec : Nat → Nat} {blocks : List Block} {first count row last : Nat}
    {longs : List Long} (before : PrefixOk spec blocks first row) (ok : ∀ long ∈ longs, long.Ok spec)
    (slice : SliceOk spec blocks first count longs row last) : PrefixOk spec blocks (first + count) last := by
  obtain ⟨matches_slice, ends⟩ := scan_sound ok slice
  obtain ⟨rows, earlier⟩ := before
  have split : blocks = blocks.take first ++ ((blocks.drop first).take count ++ (blocks.drop first).drop count) := by
    rw [List.take_append_drop, List.take_append_drop]
  have take_split : blocks.take (first + count) = blocks.take first ++ (blocks.drop first).take count := by
    rw [List.take_add]
  refine ⟨by rw [take_split, total_append, rows]; omega, fun n hn => ?_⟩
  by_cases low : n < row
  · exact earlier n low
  · have inside : n - row < total ((blocks.drop first).take count) := by omega
    rw [split, decode_append, rows, decode_append]
    simp only [low, inside, ↓reduceIte]
    rw [decode_of_matches matches_slice (n - row) inside]
    congr 1
    omega

/-- Every long block of the list satisfies `Long.Ok`. -/
def AllOk (spec : Nat → Nat) : List Long → Prop
  | [] => True
  | long :: others => long.Ok spec ∧ AllOk spec others

theorem AllOk.mem {spec : Nat → Nat} : ∀ {longs : List Long}, AllOk spec longs → ∀ long ∈ longs, long.Ok spec
  | [], _, _, member => absurd member List.not_mem_nil
  | _ :: _, ⟨first, others⟩, _, member => by
    rcases List.mem_cons.1 member with rfl | member
    · exact first
    · exact AllOk.mem others _ member

/-- The next slice extends the checked prefix. -/
theorem prefixOk_next {spec : Nat → Nat} {blocks : List Block} {first count next row last : Nat}
    {longs : List Long} (before : PrefixOk spec blocks first row)
    (slice : AllOk spec longs ∧ SliceOk spec blocks first count longs row last) (sum : first + count = next) :
    PrefixOk spec blocks next last :=
  sum ▸ prefixOk_step before slice.1.mem slice.2

end

/-! The primitive operations of the fast column formulas, in the notation that `omega` reads. -/

theorem nat_blt (a b : Nat) : Nat.blt a b = decide (a < b) := by
  cases h : Nat.blt a b
  · exact (decide_eq_false fun lt => absurd (Nat.blt_eq.mpr lt) (by simp [h])).symm
  · exact (decide_eq_true (Nat.blt_eq.mp h)).symm

theorem nat_beq (a b : Nat) : Nat.beq a b = decide (a = b) := by
  cases h : Nat.beq a b
  · exact (decide_eq_false (Nat.ne_of_beq_eq_false h)).symm
  · exact (decide_eq_true (Nat.eq_of_beq_eq_true h)).symm

theorem nat_ble (a b : Nat) : Nat.ble a b = decide (a ≤ b) := by
  cases h : Nat.ble a b
  · exact (decide_eq_false fun le => absurd (Nat.ble_eq.mpr le) (by simp [h])).symm
  · exact (decide_eq_true (Nat.ble_eq.mp h)).symm

theorem nat_add (a b : Nat) : Nat.add a b = a + b := rfl
theorem nat_sub (a b : Nat) : Nat.sub a b = a - b := rfl
theorem nat_mul (a b : Nat) : Nat.mul a b = a * b := rfl
theorem nat_div (a b : Nat) : Nat.div a b = a / b := rfl
theorem nat_mod (a b : Nat) : Nat.mod a b = a % b := rfl
theorem nat_pow (a b : Nat) : Nat.pow a b = a ^ b := rfl
theorem nat_xor (a b : Nat) : Nat.xor a b = a ^^^ b := rfl
theorem nat_land (a b : Nat) : Nat.land a b = a &&& b := rfl
theorem nat_lor (a b : Nat) : Nat.lor a b = a ||| b := rfl

/-- Fails unless the goal is an equation between natural numbers whose two sides apply the same bitwise operation
    (`^^^`, `&&&` or `|||`): the goals that `digits_eq` closes by congruence. -/
syntax "bitwise_equation" : tactic
open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| bitwise_equation) => withMainContext do
    let some (type, lhs, rhs) := (← whnfR (← getMainTarget)).eq? | throwError "bitwise_equation: not an equation"
    unless ← isDefEq type (mkConst ``Nat) do throwError "bitwise_equation: not an equation between naturals"
    let bitwise := [``HXor.hXor, ``HAnd.hAnd, ``HOr.hOr]
    unless bitwise.any (fun op => lhs.isAppOf op && rhs.isAppOf op && lhs.getAppFn == rhs.getAppFn) do
      throwError "bitwise_equation: the sides do not apply one bitwise operation"

/-- Proves `Long.Ok` for a column formula written with `pick` and `Nat.blt`: unfold the named definitions, select
    the region of the block by `omega`, and close the equation by linear arithmetic over the row digits. A block
    across a region bound falls back to a split at every bound. With a second list, a first `simp` rewrites the
    formula with these lemmas only (the column formula and its region lemmas), so that the other steps see the
    formula of one region. -/
syntax "long_ok" " [" ident,* "]" (" [" ident,* "]")? : tactic
macro_rules
  | `(tactic| long_ok [$names,*] $[[$regions,*]]?) => do
    let lemmas ← names.getElems.mapM fun name => `(Lean.Parser.Tactic.simpLemma| $name:ident)
    let select ← match regions with
      | some regions => do
        let regions ← regions.getElems.mapM fun name => `(Lean.Parser.Tactic.simpLemma| $name:ident)
        `(tactic| simp (disch := omega) only [$regions,*])
      | none => `(tactic| skip)
    `(tactic| (
      dsimp only [Long.Ok, Long.anchor]
      intro q hq j hj
      $select:tactic
      simp -failIfUnchanged (disch := omega) only [$lemmas,*, nat_blt, nat_beq, nat_ble, ← Bool.decide_and,
        ← Bool.decide_or, pick_true, pick_false, decide_true, decide_false, pick_of_true, pick_of_false, nat_add,
        nat_sub, nat_mul, nat_div, nat_mod, nat_pow, nat_xor, nat_land, nat_lor]
      first
        | omega
        | (simp only [Int.zero_mul, Int.add_zero, Nat.cast_inj]; bitwise_equation; digits_eq)
        | (simp only [pick_decide]
           split_ifs <;> first
             | omega
             | (simp only [Int.zero_mul, Int.add_zero, Nat.cast_inj]; bitwise_equation; digits_eq))))

end Airbender.Import.Setup.Scan
