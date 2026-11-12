module
public import Human.Circuits.Blake2G.Tables.Setup
public import Proven.NonVacuous.StaticTables

@[expose] public section

/-! Membership of honest rows in the modeled G setup table (the converse of `Proven/Blake2G/Tables.lean`): an XOR
    query whose entries evaluate to `a`, `b`, `a ^^^ b` and a region's tag is the row at that region's index, and a
    controller query is the row at its key. -/

namespace Airbender.NonVacuous.Blake2GSpan

theorem xor_row {width tag n a b : Nat} (high : n / 2 ^ width = a) (low : n % 2 ^ width = b) :
    Blake2G.xorRow width tag n = #v[a, b, a ^^^ b, 0, 0, 0, 0, 0, tag] := by
  simp only [Blake2G.xorRow, high, low]

/-- Setup rows below 65536: the 8-bit XOR region. -/
theorem xor8_region {control : Fin 512 → Vector Nat 7} (i : Fin 344896) (high : i.val < 65536) :
    Blake2G.setupRow control i = Blake2G.xorRow 8 4 i.val := by
  unfold Blake2G.setupRow
  dsimp only
  simp only [high, ↓reduceIte]

/-- A 8-bit XOR query (tag 4). -/
theorem xor8_contains {p : Nat} [Fact p.Prime] {control : Fin 512 → Vector Nat 7}
    {entry : Vector (Expression (ZMod p)) 9} {env : Environment (ZMod p)} {a b : Nat} (ha : a < 256) (hb : b < 256)
    (values : ∀ j : Fin 9, entry[j].eval env = ((#v[a, b, a ^^^ b, 0, 0, 0, 0, 0, 4][j] : Nat) : ZMod p)) :
    (Lookup.mk (Blake2G.setupTable control).toRaw entry).Contains env :=
  static_contains (fun _ => rfl) ((xor8_region ⟨a * 256 + b, by omega⟩ (by dsimp only; omega)).trans
    (xor_row (by dsimp only; omega) (by dsimp only; omega))) values

/-- Setup rows 65536 to 65599: the 3-bit XOR region. -/
theorem xor3_region {control : Fin 512 → Vector Nat 7} (i : Fin 344896) (low : 65536 ≤ i.val) (high : i.val < 65600) :
    Blake2G.setupRow control i = Blake2G.xorRow 3 17 (i.val - 65536) := by
  unfold Blake2G.setupRow
  dsimp only
  split_ifs <;> first | omega | rfl

/-- A 3-bit XOR query (tag 17). -/
theorem xor3_contains {p : Nat} [Fact p.Prime] {control : Fin 512 → Vector Nat 7}
    {entry : Vector (Expression (ZMod p)) 9} {env : Environment (ZMod p)} {a b : Nat} (ha : a < 8) (hb : b < 8)
    (values : ∀ j : Fin 9, entry[j].eval env = ((#v[a, b, a ^^^ b, 0, 0, 0, 0, 0, 17][j] : Nat) : ZMod p)) :
    (Lookup.mk (Blake2G.setupTable control).toRaw entry).Contains env :=
  static_contains (fun _ => rfl) ((xor3_region ⟨65536 + (a * 8 + b), by omega⟩ (by dsimp only; omega) (by dsimp only; omega)).trans
    (xor_row (by dsimp only; omega) (by dsimp only; omega))) values

/-- Setup rows 65600 to 65855: the 4-bit XOR region. -/
theorem xor4_region {control : Fin 512 → Vector Nat 7} (i : Fin 344896) (low : 65600 ≤ i.val) (high : i.val < 65856) :
    Blake2G.setupRow control i = Blake2G.xorRow 4 18 (i.val - 65600) := by
  unfold Blake2G.setupRow
  dsimp only
  split_ifs <;> first | omega | rfl

/-- A 4-bit XOR query (tag 18). -/
theorem xor4_contains {p : Nat} [Fact p.Prime] {control : Fin 512 → Vector Nat 7}
    {entry : Vector (Expression (ZMod p)) 9} {env : Environment (ZMod p)} {a b : Nat} (ha : a < 16) (hb : b < 16)
    (values : ∀ j : Fin 9, entry[j].eval env = ((#v[a, b, a ^^^ b, 0, 0, 0, 0, 0, 18][j] : Nat) : ZMod p)) :
    (Lookup.mk (Blake2G.setupTable control).toRaw entry).Contains env :=
  static_contains (fun _ => rfl) ((xor4_region ⟨65600 + (a * 16 + b), by omega⟩ (by dsimp only; omega) (by dsimp only; omega)).trans
    (xor_row (by dsimp only; omega) (by dsimp only; omega))) values

/-- Setup rows 65856 to 82239: the 7-bit XOR region. -/
theorem xor7_region {control : Fin 512 → Vector Nat 7} (i : Fin 344896) (low : 65856 ≤ i.val) (high : i.val < 82240) :
    Blake2G.setupRow control i = Blake2G.xorRow 7 19 (i.val - 65856) := by
  unfold Blake2G.setupRow
  dsimp only
  split_ifs <;> first | omega | rfl

/-- A 7-bit XOR query (tag 19). -/
theorem xor7_contains {p : Nat} [Fact p.Prime] {control : Fin 512 → Vector Nat 7}
    {entry : Vector (Expression (ZMod p)) 9} {env : Environment (ZMod p)} {a b : Nat} (ha : a < 128) (hb : b < 128)
    (values : ∀ j : Fin 9, entry[j].eval env = ((#v[a, b, a ^^^ b, 0, 0, 0, 0, 0, 19][j] : Nat) : ZMod p)) :
    (Lookup.mk (Blake2G.setupTable control).toRaw entry).Contains env :=
  static_contains (fun _ => rfl) ((xor7_region ⟨65856 + (a * 128 + b), by omega⟩ (by dsimp only; omega) (by dsimp only; omega)).trans
    (xor_row (by dsimp only; omega) (by dsimp only; omega))) values

/-- Setup rows 82240 to 344383: the 9-bit XOR region. -/
theorem xor9_region {control : Fin 512 → Vector Nat 7} (i : Fin 344896) (low : 82240 ≤ i.val) (high : i.val < 344384) :
    Blake2G.setupRow control i = Blake2G.xorRow 9 20 (i.val - 82240) := by
  unfold Blake2G.setupRow
  dsimp only
  split_ifs <;> first | omega | rfl

/-- A 9-bit XOR query (tag 20). -/
theorem xor9_contains {p : Nat} [Fact p.Prime] {control : Fin 512 → Vector Nat 7}
    {entry : Vector (Expression (ZMod p)) 9} {env : Environment (ZMod p)} {a b : Nat} (ha : a < 512) (hb : b < 512)
    (values : ∀ j : Fin 9, entry[j].eval env = ((#v[a, b, a ^^^ b, 0, 0, 0, 0, 0, 20][j] : Nat) : ZMod p)) :
    (Lookup.mk (Blake2G.setupTable control).toRaw entry).Contains env :=
  static_contains (fun _ => rfl) ((xor9_region ⟨82240 + (a * 512 + b), by omega⟩ (by dsimp only; omega) (by dsimp only; omega)).trans
    (xor_row (by dsimp only; omega) (by dsimp only; omega))) values

/-- Setup rows 344384 onwards: the controller region, keyed by the row offset. -/
theorem control_region {control : Fin 512 → Vector Nat 7} (i : Fin 344896) (low : 344384 ≤ i.val) :
    Blake2G.setupRow control i = #v[i.val - 344384, (control ⟨i.val - 344384, by omega⟩)[0],
      (control ⟨i.val - 344384, by omega⟩)[1], (control ⟨i.val - 344384, by omega⟩)[2],
      (control ⟨i.val - 344384, by omega⟩)[3], (control ⟨i.val - 344384, by omega⟩)[4],
      (control ⟨i.val - 344384, by omega⟩)[5], (control ⟨i.val - 344384, by omega⟩)[6], 28] := by
  unfold Blake2G.setupRow
  dsimp only
  split_ifs <;> first | omega | rfl

/-- The controller query at `key`. -/
theorem control_contains {p : Nat} [Fact p.Prime] {control : Fin 512 → Vector Nat 7}
    {entry : Vector (Expression (ZMod p)) 9} {env : Environment (ZMod p)} (key : Fin 512)
    (values : ∀ j : Fin 9, entry[j].eval env =
      ((#v[key.val, (control key)[0], (control key)[1], (control key)[2], (control key)[3], (control key)[4],
        (control key)[5], (control key)[6], 28][j] : Nat) : ZMod p)) :
    (Lookup.mk (Blake2G.setupTable control).toRaw entry).Contains env := by
  obtain ⟨i, index⟩ : ∃ i : Fin 344896, i.val = 344384 + key.val := ⟨⟨344384 + key.val, by omega⟩, rfl⟩
  have selected : (⟨i.val - 344384, by omega⟩ : Fin 512) = key := Fin.ext (by simp only [index]; omega)
  refine static_contains (fun _ => rfl) (i := i) ?_ values
  rw [control_region i (by omega), selected, show i.val - 344384 = key.val by omega]

end Airbender.NonVacuous.Blake2GSpan
