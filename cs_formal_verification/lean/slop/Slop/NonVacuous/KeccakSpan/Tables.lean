module
public import Slop.NonVacuous.KeccakSpan.Honest
public import Slop.NonVacuous.StaticTables
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/-! Membership of an honest operation's lookups in the modeled Keccak setup table (the converse of
    `Slop/Keccak/Tables.lean`): a byte lookup is the byte row at its index (XOR 4, Iota XOR 38, ANDN 39), a
    rotation lookup the rotation row at its key (tag 40), and the controller query the row at its key. An honest
    operation of valid operands also has 16-bit results. -/

namespace Airbender.NonVacuous.KeccakSpan

variable {p : Nat} [Fact p.Prime]

/-- Setup rows by region: the XOR rows (tag 4), Iota XOR (38), ANDN (39), rotations (40). -/
private theorem xor_region {control : Fin 4096 → Vector Nat 6} (i : Fin 1249281) (low : 1 ≤ i.val)
    (high : i.val < 65537) : Keccak.setupRow control i = Keccak.byteRow 4 (i.val - 1) := by
  unfold Keccak.setupRow
  dsimp only
  split_ifs <;> first | omega | rfl

private theorem iota_region {control : Fin 4096 → Vector Nat 6} (i : Fin 1249281) (low : 69633 ≤ i.val)
    (high : i.val < 135169) : Keccak.setupRow control i = Keccak.byteRow 38 (i.val - 69633) := by
  unfold Keccak.setupRow
  dsimp only
  split_ifs <;> first | omega | rfl

private theorem andn_region {control : Fin 4096 → Vector Nat 6} (i : Fin 1249281) (low : 135169 ≤ i.val)
    (high : i.val < 200705) : Keccak.setupRow control i = Keccak.byteRow 39 (i.val - 135169) := by
  unfold Keccak.setupRow
  dsimp only
  split_ifs <;> first | omega | rfl

private theorem rotation_region {control : Fin 4096 → Vector Nat 6} (i : Fin 1249281) (low : 200705 ≤ i.val) :
    Keccak.setupRow control i = Keccak.rotationRow (i.val - 200705) := by
  unfold Keccak.setupRow
  dsimp only
  split_ifs <;> first | omega | rfl

private theorem byte_row (tag : Nat) {a b n : Nat} (high : n / 256 = (if tag = 4 then a else b))
    (low : n % 256 = (if tag = 4 then b else a)) :
    Keccak.byteRow tag n = #v[a, b, byteOp tag a b, 0, 0, 0, 0, tag] := by
  unfold Keccak.byteRow byteOp
  by_cases four : tag = 4
  · subst four
    simp only [↓reduceIte] at high low
    simp only [↓reduceIte, high, low, Nat.reduceEqDiff]
  · simp only [four, ↓reduceIte] at high low
    simp only [four, ↓reduceIte, high, low]

private theorem xor_row {control : Fin 4096 → Vector Nat 6} {a b : Nat} (ha : a < 256) (hb : b < 256) :
    Keccak.setupRow control ⟨1 + (256 * a + b), by omega⟩ = #v[a, b, byteOp 4 a b, 0, 0, 0, 0, 4] :=
  (xor_region _ (by dsimp only; omega) (by dsimp only; omega)).trans
    (byte_row 4 (by simp only [↓reduceIte]; omega) (by simp only [↓reduceIte]; omega))

private theorem iota_row {control : Fin 4096 → Vector Nat 6} {a b : Nat} (ha : a < 256) (hb : b < 256) :
    Keccak.setupRow control ⟨69633 + (a + 256 * b), by omega⟩ = #v[a, b, byteOp 38 a b, 0, 0, 0, 0, 38] :=
  (iota_region _ (by dsimp only; omega) (by dsimp only; omega)).trans
    (byte_row 38 (by simp only [Nat.reduceEqDiff, ↓reduceIte]; omega)
      (by simp only [Nat.reduceEqDiff, ↓reduceIte]; omega))

private theorem andn_row {control : Fin 4096 → Vector Nat 6} {a b : Nat} (ha : a < 256) (hb : b < 256) :
    Keccak.setupRow control ⟨135169 + (a + 256 * b), by omega⟩ = #v[a, b, byteOp 39 a b, 0, 0, 0, 0, 39] :=
  (andn_region _ (by dsimp only; omega) (by dsimp only; omega)).trans
    (byte_row 39 (by simp only [Nat.reduceEqDiff, ↓reduceIte]; omega)
      (by simp only [Nat.reduceEqDiff, ↓reduceIte]; omega))

private theorem rotation_key {n word shift : Nat} (low : n % 65536 = word) (high : n / 65536 = shift) :
    Keccak.rotationRow n = #v[n, word / 2 ^ (16 - shift), word * 2 ^ shift % 65536, 0, 0, 0, 0, 40] := by
  unfold Keccak.rotationRow
  simp only [low, high]

/-- A rotation query of a 16-bit word and a shift below 16 is the rotation row at its key. -/
private theorem rotation_contains {control : Fin 4096 → Vector Nat 6} {entry : Vector (Expression (ZMod p)) 8}
    {env : Environment (ZMod p)} {word shift : Nat} (hw : word < 65536) (hs : shift < 16)
    (values : ∀ j : Fin 8, entry[j].eval env = ((#v[word + 65536 * shift, word / 2 ^ (16 - shift),
      word * 2 ^ shift % 65536, 0, 0, 0, 0, 40][j] : Nat) : ZMod p)) :
    (Lookup.mk (Keccak.setupTable control).toRaw entry).Contains env := by
  obtain ⟨i, index⟩ : ∃ i : Fin 1249281, i.val = 200705 + (word + 65536 * shift) := ⟨⟨_, by omega⟩, rfl⟩
  have row : Keccak.setupRow control i =
      #v[word + 65536 * shift, word / 2 ^ (16 - shift), word * 2 ^ shift % 65536, 0, 0, 0, 0, 40] := by
    rw [rotation_region i (by omega), rotation_key (n := i.val - 200705) (word := word) (shift := shift)
      (by omega) (by omega), show i.val - 200705 = word + 65536 * shift by omega]
  exact static_contains (fun _ => rfl) row values

/-- An operation's operands are 16-bit limbs, and a byte operation's tag is a byte table's. -/
structure Op.Valid (o : Op) : Prop where
  A : ∀ j < 4, o.A j < 65536
  B : o.rot = false → ∀ j < 4, o.B j < 65536
  tag : o.rot = false → o.tag = 4 ∨ o.tag = 38 ∨ o.tag = 39

theorem byteOp_lt {tag a b : Nat} (ha : a < 256) (hb : b < 256) : byteOp tag a b < 256 := by
  unfold byteOp
  split_ifs
  · exact Nat.xor_lt_two_pow (n := 8) ha (Nat.mod_lt _ (by decide))
  · exact lt_of_le_of_lt Nat.and_le_right hb
  · exact Nat.xor_lt_two_pow (n := 8) ha hb

/-- The entries of a valid operation's byte lookups are bytes. -/
theorem Op.Valid.bytes {o : Op} (valid : o.Valid) (rot : o.rot = false) {i : Nat} (hi : i < 8) :
    o.a i < 256 ∧ o.b i < 256 := by
  have hA := valid.A (i / 2) (by omega)
  have hB := valid.B rot (i / 2) (by omega)
  simp only [Op.a, Op.b, rot, Bool.false_eq_true, ↓reduceIte]
  constructor <;> split_ifs <;> omega

/-- Each of a valid operation's eight lookups is a row of the modeled setup table. -/
theorem Op.Valid.contains {o : Op} (valid : o.Valid) {control : Fin 4096 → Vector Nat 6}
    {entry : Vector (Expression (ZMod p)) 8} {env : Environment (ZMod p)} {i : Nat} (hi : i < 8)
    (values : ∀ j : Fin 8,
      entry[j].eval env = ((#v[o.a i, o.b i, o.c i, 0, 0, 0, 0, o.tagValue][j] : Nat) : ZMod p)) :
    (Lookup.mk (Keccak.setupTable control).toRaw entry).Contains env := by
  cases rot : o.rot
  · obtain ⟨ha, hb⟩ := valid.bytes rot hi
    have c : o.c i = byteOp o.tag (o.a i) (o.b i) := by simp only [Op.c, rot, Bool.false_eq_true, ↓reduceIte]
    have tag : o.tagValue = o.tag := by simp only [Op.tagValue, rot, Bool.false_eq_true, ↓reduceIte]
    rw [c, tag] at values
    rcases valid.tag rot with known | known | known <;> rw [known] at values
    · exact static_contains (fun _ => rfl) (xor_row ha hb) values
    · exact static_contains (fun _ => rfl) (iota_row ha hb) values
    · exact static_contains (fun _ => rfl) (andn_row ha hb) values
  · have tag : o.tagValue = 40 := by simp only [Op.tagValue, rot, ↓reduceIte]
    have shift : o.shift < 16 := Nat.mod_lt _ (by decide)
    by_cases low : i < 4
    · have hA := valid.A i low
      have a : o.a i = o.A i + 65536 * o.shift := by simp only [Op.a, rot, low, ↓reduceIte]
      have b : o.b i = o.A i / 2 ^ (16 - o.shift) := by simp only [Op.b, rot, low, ↓reduceIte]
      have c : o.c i = o.A i * 2 ^ o.shift % 65536 := by simp only [Op.c, rot, low, ↓reduceIte]
      rw [a, b, c, tag] at values
      exact rotation_contains hA shift values
    · have a : o.a i = 0 + 65536 * 0 := by simp only [Op.a, rot, low, ↓reduceIte]
      have b : o.b i = 0 / 2 ^ (16 - 0) := by simp only [Op.b, rot, low, ↓reduceIte, Nat.zero_div]
      have c : o.c i = 0 * 2 ^ 0 % 65536 := by simp only [Op.c, rot, low, ↓reduceIte, zero_mul, Nat.zero_mod]
      rw [a, b, c, tag] at values
      exact rotation_contains (by decide) (by decide) values

/-- A valid operation's result limbs are 16-bit. -/
theorem Op.Valid.out_lt {o : Op} (valid : o.Valid) {j : Nat} (hj : j < 4) : o.out j < 65536 := by
  cases rot : o.rot
  · obtain ⟨a0, b0⟩ := valid.bytes rot (i := 2 * j) (by omega)
    obtain ⟨a1, b1⟩ := valid.bytes rot (i := 2 * j + 1) (by omega)
    have c0 := byteOp_lt (tag := o.tag) a0 b0
    have c1 := byteOp_lt (tag := o.tag) a1 b1
    simp only [Op.out, Op.c, rot, Bool.false_eq_true, ↓reduceIte]
    omega
  · have shift : o.shift < 16 := Nat.mod_lt _ (by decide)
    have low (i : Nat) : (j + 4 - o.limbs) % 4 < 4 ∧ (j + 3 - o.limbs) % 4 < 4 :=
      ⟨Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide)⟩
    have hc := valid.A ((j + 4 - o.limbs) % 4) (low 0).1
    have hb := valid.A ((j + 3 - o.limbs) % 4) (low 0).2
    simp only [Op.out, Op.c, Op.b, rot, ↓reduceIte, (low 0).1, (low 0).2]
    generalize o.A ((j + 4 - o.limbs) % 4) = u at hc ⊢
    generalize o.A ((j + 3 - o.limbs) % 4) = v at hb ⊢
    generalize o.shift = s at shift ⊢
    interval_cases s <;> omega

/-- Setup rows 65537 to 69632: the controller region, keyed by the row offset. -/
private theorem control_region {control : Fin 4096 → Vector Nat 6} (i : Fin 1249281) (low : 65537 ≤ i.val)
    (high : i.val < 69633) :
    Keccak.setupRow control i = #v[i.val - 65537, (control ⟨i.val - 65537, by omega⟩)[0],
      (control ⟨i.val - 65537, by omega⟩)[1], (control ⟨i.val - 65537, by omega⟩)[2],
      (control ⟨i.val - 65537, by omega⟩)[3], (control ⟨i.val - 65537, by omega⟩)[4],
      (control ⟨i.val - 65537, by omega⟩)[5], 37] := by
  unfold Keccak.setupRow
  dsimp only
  split_ifs <;> first | omega | rfl

/-- The controller query at `key`: the key, the six lane indices and tag 37. -/
theorem control_contains {control : Fin 4096 → Vector Nat 6} {entry : Vector (Expression (ZMod p)) 8}
    {env : Environment (ZMod p)} (key : Fin 4096)
    (values : ∀ j : Fin 8, entry[j].eval env = ((#v[key.val, (control key)[0], (control key)[1], (control key)[2],
      (control key)[3], (control key)[4], (control key)[5], 37][j] : Nat) : ZMod p)) :
    (Lookup.mk (Keccak.setupTable control).toRaw entry).Contains env := by
  obtain ⟨i, index⟩ : ∃ i : Fin 1249281, i.val = 65537 + key.val := ⟨⟨_, by omega⟩, rfl⟩
  have selected : (⟨i.val - 65537, by omega⟩ : Fin 4096) = key := Fin.ext (by simp only [index]; omega)
  refine static_contains (fun _ => rfl) (i := i) ?_ values
  rw [control_region i (by omega) (by omega), selected, show i.val - 65537 = key.val by omega]

end Airbender.NonVacuous.KeccakSpan
