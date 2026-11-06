import Slop.Keccak.Lookups
import Slop.Keccak.OpIndex
import Slop.Eval
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases

/-! Completeness of the forty byte queries, proved once for every row (lean-strategies §2.1):
the query's value columns, the setup rows of each tag at their index, and membership from those. -/

namespace Airbender.Keccak.Proofs
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 16384

/-- Value column `part` (input, input, output) of byte query `i`: operation `i / 8`, byte `i % 8`. -/
def byteColumn (part : Fin 3) (i : Fin 40) : Nat := 102 + 8 * part.val + 24 * (i.val / 8) + i.val % 8

theorem byte_entry_values {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 8))
    (w : Nat → ZMod p) (i : Fin 40) :
    (byteEntry setup i).map (Expression.eval (Verification.environment w)) =
      #v[w (byteColumn 0 i), w (byteColumn 1 i), w (byteColumn 2 i), 0, 0, 0, 0, byteTag setup w i] := by
  have tag : byteTag setup w i = ((byteQuery setup i).entry.toArray[7]!).eval (Verification.environment w) := by
    unfold byteTag
    simp only [Array.back!, Vector.size_toArray, byte_query_arity]
  rw [tag, ← Vector.toArray_inj, Vector.toArray_map, byteEntry, Vector.toArray_cast]
  fin_cases i
  all_goals simp only [byteQuery, byteColumn]
  all_goals op_index
  all_goals eval_entry [Fin.val_mk, Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul, Nat.zero_div,
    Nat.div_self, and_self, Nat.reduceLT, Nat.ofNat_pos, Nat.one_lt_ofNat, Vector.toArray_mk]

private theorem setup_row_low {control : Fin 4096 → Vector Nat 6} {n : Nat} (h : n < 1249281)
    (pos : 0 < n) (low : n < 65537) : setupRow control ⟨n, h⟩ = byteRow 4 (n - 1) := by
  unfold setupRow
  rw [ite_eq_right (Nat.ne_of_gt pos), ite_eq_left low]

private theorem byte_row_four {a b : Nat} (hb : b < 256) :
    byteRow 4 (256 * a + b) = #v[a, b, a ^^^ b, 0, 0, 0, 0, 4] := by
  have d : (256 * a + b) / 256 = a := by omega
  have m : (256 * a + b) % 256 = b := by omega
  unfold byteRow
  simp only [d, m, ↓reduceIte]
  rfl

private theorem byte_row_iota {a b : Nat} (ha : a < 256) :
    byteRow 38 (a + 256 * b) = #v[a, b, a ^^^ iotaByte b, 0, 0, 0, 0, 38] := by
  have d : (a + 256 * b) / 256 = b := by omega
  have m : (a + 256 * b) % 256 = a := by omega
  unfold byteRow
  simp only [d, m, ↓reduceIte, show (38 : Nat) ≠ 4 by decide]

private theorem byte_row_andn {a b : Nat} (ha : a < 256) :
    byteRow 39 (a + 256 * b) = #v[a, b, (a ^^^ 255) &&& b, 0, 0, 0, 0, 39] := by
  have d : (a + 256 * b) / 256 = b := by omega
  have m : (a + 256 * b) % 256 = a := by omega
  unfold byteRow
  simp only [d, m, ↓reduceIte, show (39 : Nat) ≠ 4 by decide, show (39 : Nat) ≠ 38 by decide]

theorem setup_row_xor (control : Fin 4096 → Vector Nat 6) {a b : Nat} (ha : a < 256) (hb : b < 256) :
    setupRow control ⟨1 + 256 * a + b, by omega⟩ = #v[a, b, a ^^^ b, 0, 0, 0, 0, 4] := by
  rw [setup_row_low _ (by omega) (by omega), show 1 + 256 * a + b - 1 = 256 * a + b by omega]
  exact byte_row_four hb

theorem setup_row_iota (control : Fin 4096 → Vector Nat 6) {a b : Nat} (ha : a < 256) (hb : b < 256) :
    setupRow control ⟨69633 + a + 256 * b, by omega⟩ = #v[a, b, a ^^^ iotaByte b, 0, 0, 0, 0, 38] := by
  unfold setupRow
  rw [ite_eq_right (show 69633 + a + 256 * b ≠ 0 by omega),
    ite_eq_right (show ¬ 69633 + a + 256 * b < 65537 by omega),
    dite_eq_right (show ¬ 69633 + a + 256 * b < 69633 by omega),
    ite_eq_left (show 69633 + a + 256 * b < 135169 by omega),
    show 69633 + a + 256 * b - 69633 = a + 256 * b by omega]
  exact byte_row_iota ha

theorem setup_row_andn (control : Fin 4096 → Vector Nat 6) {a b : Nat} (ha : a < 256) (hb : b < 256) :
    setupRow control ⟨135169 + a + 256 * b, by omega⟩ =
      #v[a, b, (a ^^^ 255) &&& b, 0, 0, 0, 0, 39] := by
  unfold setupRow
  rw [ite_eq_right (show 135169 + a + 256 * b ≠ 0 by omega),
    ite_eq_right (show ¬ 135169 + a + 256 * b < 65537 by omega),
    dite_eq_right (show ¬ 135169 + a + 256 * b < 69633 by omega),
    ite_eq_right (show ¬ 135169 + a + 256 * b < 135169 by omega),
    ite_eq_left (show 135169 + a + 256 * b < 200705 by omega),
    show 135169 + a + 256 * b - 135169 = a + 256 * b by omega]
  exact byte_row_andn ha

theorem setup_row_rotation (control : Fin 4096 → Vector Nat 6) {key : Nat} (h : key < 1048576) :
    setupRow control ⟨200705 + key, by omega⟩ = rotationRow key := by
  unfold setupRow
  rw [ite_eq_right (show 200705 + key ≠ 0 by omega),
    ite_eq_right (show ¬ 200705 + key < 65537 by omega),
    dite_eq_right (show ¬ 200705 + key < 69633 by omega),
    ite_eq_right (show ¬ 200705 + key < 135169 by omega),
    ite_eq_right (show ¬ 200705 + key < 200705 by omega),
    show 200705 + key - 200705 = key by omega]

/-- A byte query holds when its value columns and tag are a setup row's first three and last entries. -/
theorem byte_query_of_row {p : Nat} [Fact p.Prime] {control : Fin 4096 → Vector Nat 6}
    {w : Nat → ZMod p} (i : Fin 40) (index : Fin 1249281) {a b c t : Nat}
    (row : setupRow control index = #v[a, b, c, 0, 0, 0, 0, t])
    (ha : w (byteColumn 0 i) = a) (hb : w (byteColumn 1 i) = b) (hc : w (byteColumn 2 i) = c)
    (ht : byteTag (setupTable control) w i = t) :
    (byteQuery (setupTable control) i).Contains (Verification.environment w) := by
  rw [byte_query_shape]
  refine ⟨index, ?_⟩
  change (byteEntry (setupTable control) i).map (Expression.eval (Verification.environment w)) =
    (setupRow control index).map (fun (n : Nat) => (n : ZMod p))
  rw [byte_entry_values, row, ha, hb, hc, ht]
  apply Vector.ext
  intro j hj
  rw [Vector.getElem_map]
  interval_cases j <;> simp

/-- A row whose byte-query value columns (102 to 221) are `bytes part i` and whose other columns are `base`. -/
def bytesRow {p : Nat} (base : Nat → ZMod p) (bytes : Fin 3 → Fin 40 → Nat) (v : Nat) : ZMod p :=
  if 102 ≤ v ∧ v < 222 then
    (bytes ⟨(v - 102) % 24 / 8 % 3, Nat.mod_lt _ (by decide)⟩
      ⟨((v - 102) / 24 * 8 + (v - 102) % 8) % 40, Nat.mod_lt _ (by decide)⟩ : Nat)
  else base v

theorem bytes_row_byte {p : Nat} (base : Nat → ZMod p) (bytes : Fin 3 → Fin 40 → Nat)
    (part : Fin 3) (i : Fin 40) : bytesRow base bytes (byteColumn part i) = (bytes part i : Nat) := by
  have range : 102 ≤ byteColumn part i ∧ byteColumn part i < 222 := by
    unfold byteColumn; omega
  have hp : (⟨(byteColumn part i - 102) % 24 / 8 % 3, Nat.mod_lt _ (by decide)⟩ : Fin 3) = part := by
    apply Fin.ext; have := part.isLt; have := i.isLt; simp only [byteColumn, Fin.val_mk]; omega
  have hi : (⟨((byteColumn part i - 102) / 24 * 8 + (byteColumn part i - 102) % 8) % 40,
      Nat.mod_lt _ (by decide)⟩ : Fin 40) = i := by
    apply Fin.ext; have := part.isLt; have := i.isLt; simp only [byteColumn, Fin.val_mk]; omega
  unfold bytesRow
  rw [ite_eq_left range, hp, hi]

/-- The routing tag of operation `op` in mode `mode`. -/
def operationTag (mode : Fin 7) (op : Fin 5) : Nat := operationTags[mode][op]

/-- With one selected mode column, each byte query's tag is that mode's routing tag. -/
theorem byte_tag_of_mode {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 8))
    {w : Nat → ZMod p} (mode : Fin 7)
    (modes : ∀ j : Fin 7, w Variables.modeColumns[j] = if j = mode then 1 else 0) (i : Fin 40) :
    byteTag setup w i = (operationTag mode ⟨i.val / 8, by omega⟩ : Nat) := by
  rw [tag_polynomial]
  simp only [modes, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rfl

/-- Byte `k` of a word. -/
def wordByte (x k : Nat) : Nat := x / 2 ^ (8 * k) % 256

theorem word_byte_lt (x k : Nat) : wordByte x k < 256 := Nat.mod_lt _ (by decide)

theorem word_byte_xor (x y k : Nat) : wordByte (x ^^^ y) k = wordByte x k ^^^ wordByte y k := by
  unfold wordByte
  rw [Nat.xor_div_two_pow, show (256 : Nat) = 2 ^ 8 from rfl, Nat.xor_mod_two_pow]

/-- An XOR-routed byte query holds on the bytes of two words and of their XOR. -/
theorem xor_query {p : Nat} [Fact p.Prime] {control : Fin 4096 → Vector Nat 6}
    {w : Nat → ZMod p} (i : Fin 40) (x y : Nat)
    (ha : w (byteColumn 0 i) = (wordByte x (i.val % 8) : Nat))
    (hb : w (byteColumn 1 i) = (wordByte y (i.val % 8) : Nat))
    (hc : w (byteColumn 2 i) = (wordByte (x ^^^ y) (i.val % 8) : Nat))
    (ht : byteTag (setupTable control) w i = (4 : Nat)) :
    (byteQuery (setupTable control) i).Contains (Verification.environment w) := by
  rw [word_byte_xor] at hc
  exact byte_query_of_row i _
    (setup_row_xor control (word_byte_lt x _) (word_byte_lt y _)) ha hb hc ht

/-- A rotation-routed query holds on a 16-bit limb, a shift below 16 and the two rotated pieces. -/
theorem rotation_query {p : Nat} [Fact p.Prime] {control : Fin 4096 → Vector Nat 6}
    {w : Nat → ZMod p} (i : Fin 40) {limb shift : Nat} (hl : limb < 65536) (hs : shift < 16)
    (ha : w (byteColumn 0 i) = (limb + 65536 * shift : Nat))
    (hb : w (byteColumn 1 i) = (limb / 2 ^ (16 - shift) : Nat))
    (hc : w (byteColumn 2 i) = (limb * 2 ^ shift % 65536 : Nat))
    (ht : byteTag (setupTable control) w i = (40 : Nat)) :
    (byteQuery (setupTable control) i).Contains (Verification.environment w) := by
  have mod : (limb + 65536 * shift) % 65536 = limb := by omega
  have div : (limb + 65536 * shift) / 65536 = shift := by omega
  refine byte_query_of_row i _ (setup_row_rotation control (key := limb + 65536 * shift) (by omega)) ha ?_ ?_ ht
  · simpa only [rotationRow, mod, div] using hb
  · simpa only [rotationRow, mod, div] using hc

/-- A rotation-routed query holds on an all-zero row (the padding key). -/
theorem rotation_zero_query {p : Nat} [Fact p.Prime] {control : Fin 4096 → Vector Nat 6}
    {w : Nat → ZMod p} (i : Fin 40)
    (ha : w (byteColumn 0 i) = 0) (hb : w (byteColumn 1 i) = 0) (hc : w (byteColumn 2 i) = 0)
    (ht : byteTag (setupTable control) w i = (40 : Nat)) :
    (byteQuery (setupTable control) i).Contains (Verification.environment w) :=
  rotation_query i (limb := 0) (shift := 0) (by decide) (by decide)
    (by simpa using ha) (by simpa using hb) (by simpa using hc) ht

theorem word_byte_andn (x y : Nat) {k : Nat} (hk : k < 8) :
    wordByte (not64 x &&& y) k = (wordByte x k ^^^ 255) &&& wordByte y k := by
  have mask : wordByte 0xffffffffffffffff k = 255 := by interval_cases k <;> decide
  unfold not64
  rw [← mask, ← word_byte_xor]
  unfold wordByte
  rw [Nat.and_div_two_pow, show (256 : Nat) = 2 ^ 8 from rfl, Nat.and_mod_two_pow]

/-- An ANDN-routed byte query holds on the bytes of two words and of `not a and b`. -/
theorem andn_query {p : Nat} [Fact p.Prime] {control : Fin 4096 → Vector Nat 6}
    {w : Nat → ZMod p} (i : Fin 40) (x y : Nat)
    (ha : w (byteColumn 0 i) = (wordByte x (i.val % 8) : Nat))
    (hb : w (byteColumn 1 i) = (wordByte y (i.val % 8) : Nat))
    (hc : w (byteColumn 2 i) = (wordByte (not64 x &&& y) (i.val % 8) : Nat))
    (ht : byteTag (setupTable control) w i = (39 : Nat)) :
    (byteQuery (setupTable control) i).Contains (Verification.environment w) := by
  rw [word_byte_andn x y (Nat.mod_lt _ (by decide))] at hc
  exact byte_query_of_row i _
    (setup_row_andn control (word_byte_lt x _) (word_byte_lt y _)) ha hb hc ht

theorem iota_byte_round {round k : Nat} (hr : round < 32) :
    iotaByte (round + 32 * k) = wordByte (adjustedConstant round) k := by
  unfold iotaByte wordByte
  rw [show (round + 32 * k) % 32 = round by omega, show (round + 32 * k) / 32 = k by omega]

/-- An Iota-routed byte query holds on a word's byte, the round-and-byte control and the
    byte of the word XOR the round constant. -/
theorem iota_query {p : Nat} [Fact p.Prime] {control : Fin 4096 → Vector Nat 6}
    {w : Nat → ZMod p} (i : Fin 40) (x : Nat) {round : Nat} (hr : round < 32)
    (ha : w (byteColumn 0 i) = (wordByte x (i.val % 8) : Nat))
    (hb : w (byteColumn 1 i) = (round + 32 * (i.val % 8) : Nat))
    (hc : w (byteColumn 2 i) = (wordByte (x ^^^ adjustedConstant round) (i.val % 8) : Nat))
    (ht : byteTag (setupTable control) w i = (38 : Nat)) :
    (byteQuery (setupTable control) i).Contains (Verification.environment w) := by
  rw [word_byte_xor, ← iota_byte_round hr] at hc
  have hk : i.val % 8 < 8 := Nat.mod_lt _ (by decide)
  exact byte_query_of_row i _
    (setup_row_iota control (word_byte_lt x _) (by omega : round + 32 * (i.val % 8) < 256)) ha hb hc ht

theorem setup_row_controller (control : Fin 4096 → Vector Nat 6) {key : Nat} (h : key < 4096) :
    setupRow control ⟨65537 + key, by omega⟩ =
      #v[key, (control ⟨key, h⟩)[0], (control ⟨key, h⟩)[1], (control ⟨key, h⟩)[2],
        (control ⟨key, h⟩)[3], (control ⟨key, h⟩)[4], (control ⟨key, h⟩)[5], 37] := by
  unfold setupRow
  rw [ite_eq_right (show 65537 + key ≠ 0 by omega),
    ite_eq_right (show ¬ 65537 + key < 65537 by omega),
    dite_eq_left (show 65537 + key < 69633 by omega)]
  simp only [show 65537 + key - 65537 = key by omega]

theorem controller_arity {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 8)) :
    ((FlatOperation.lookups (importedConstraints setup)).get
      ⟨1, by rw [lookup_count]; decide⟩).table.arity = 8 := rfl

/-- The controller query's entry, at its checked width. -/
def controllerEntry {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 8)) :
    Vector (Expression (ZMod p)) 8 :=
  ((FlatOperation.lookups (importedConstraints setup)).get
    ⟨1, by rw [lookup_count]; decide⟩).entry.cast (controller_arity setup)

theorem controller_query_shape {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 8)) :
    (FlatOperation.lookups (importedConstraints setup)).get ⟨1, by rw [lookup_count]; decide⟩ =
      Lookup.mk setup.toRaw (controllerEntry setup) := rfl

/-- The controller query holds when its packed key and six outputs are a controller row. -/
theorem controller_query {p : Nat} [Fact p.Prime] {control : Fin 4096 → Vector Nat 6}
    {w : Nat → ZMod p} {key : Nat} (h : key < 4096)
    (packed : 2048 * w 0 + w 3 = (key : Nat))
    (outputs : w 7 = ((control ⟨key, h⟩)[0] : Nat) ∧ w 8 = ((control ⟨key, h⟩)[1] : Nat) ∧
      w 9 = ((control ⟨key, h⟩)[2] : Nat) ∧ w 10 = ((control ⟨key, h⟩)[3] : Nat) ∧
      w 11 = ((control ⟨key, h⟩)[4] : Nat) ∧ w 12 = ((control ⟨key, h⟩)[5] : Nat)) :
    ((FlatOperation.lookups (importedConstraints (setupTable control))).get
      ⟨1, by rw [lookup_count]; decide⟩).Contains (Verification.environment w) := by
  rw [controller_query_shape]
  change ∃ index : Fin 1249281,
    (controllerEntry (setupTable control)).map (Expression.eval (Verification.environment w)) =
      (setupRow control index).map (fun (n : Nat) => (n : ZMod p))
  refine ⟨⟨65537 + key, by omega⟩, ?_⟩
  obtain ⟨o0, o1, o2, o3, o4, o5⟩ := outputs
  rw [← Vector.toArray_inj, Vector.toArray_map, Vector.toArray_map, controllerEntry, Vector.toArray_cast,
    setup_row_controller control h]
  op_index
  eval_entry [Vector.toArray_mk]
  simp only [packed, o0, o1, o2, o3, o4, o5]

end Airbender.Keccak.Proofs
