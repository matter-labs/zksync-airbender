module
public import Proven.NonVacuous.KeccakSpan.Block
public import Proven.NonVacuous.KeccakSpan.Row
public import Proven.NonVacuous.SequentialRun

@[expose] public section

/-! The fourteen memory ports of a Keccak row (`Keccak.importedConstraintsMemoryPorts`, by evaluation of the
    imported layout) and the honest columns they read and write: x10 (the control word, written with the next
    one), x11 (the state pointer, read only), and the low and high word of each of the six lanes, at the pointer
    plus eight times the lane plus four times the word. Under the span invariant every port reads its cell's
    current token. -/

namespace Airbender.NonVacuous.KeccakSpan
open Arithmetic Trace

local notation "P" => babyBearModulus

theorem port_zero : Keccak.importedConstraintsMemoryPorts[0]'(by decide) =
    ⟨⟨2, #v[222, 223], 224⟩, .constantRegister 10, .u16 #v[3, 4], some (.u16 #v[5, 6])⟩ := by decide

theorem port_one : Keccak.importedConstraintsMemoryPorts[1]'(by decide) =
    ⟨⟨2, #v[225, 226], 227⟩, .constantRegister 11, .u16 #v[13, 14], none⟩ := by decide

theorem port_lane : ∀ i : Fin 12, Keccak.importedConstraintsMemoryPorts[2 + i.val]'(by change _ < 14; omega) =
    ⟨⟨2, #v[228 + 3 * i.val, 229 + 3 * i.val], 230 + 3 * i.val⟩,
      .indirect ⟨11, i.val, #v[13, 14], 8, some (7 + i.val / 2), 4 * (i.val % 2), #v[15 + 4 * i.val, 16 + 4 * i.val],
        some #v[17 + 4 * i.val, 18 + 4 * i.val]⟩,
      .u16 #v[15 + 4 * i.val, 16 + 4 * i.val], some (.u16 #v[17 + 4 * i.val, 18 + 4 * i.val])⟩ := by decide

namespace RowInput
variable {p : Nat} (x : RowInput)

/-- The read and written limbs of lane port `i` (lane `i / 2`, word `i % 2`). -/
theorem assignment_read_low {i : Nat} (hi : i < 12) :
    x.assignment (p := p) (15 + 4 * i) = ((x.read (i / 2) (2 * (i % 2)) : Nat) : ZMod p) := by
  obtain ⟨l, h, small, rfl⟩ : ∃ l h, h < 2 ∧ i = 2 * l + h :=
    ⟨i / 2, i % 2, Nat.mod_lt _ (by decide), by omega⟩
  interval_cases h <;>
  simp only [RowInput.assignment, RowInput.column, RowInput.lanePort, show ¬15 + 4 * (2 * l + 0) < 15 by omega,
    show 15 + 4 * (2 * l + 0) < 63 by omega, show (15 + 4 * (2 * l + 0) - 15) / 8 = l by omega,
    show (15 + 4 * (2 * l + 0) - 15) % 8 = 0 by omega, show (2 * l + 0) / 2 = l by omega,
    show (2 * l + 0) % 2 = 0 by omega, show ¬15 + 4 * (2 * l + 1) < 15 by omega,
    show 15 + 4 * (2 * l + 1) < 63 by omega, show (15 + 4 * (2 * l + 1) - 15) / 8 = l by omega,
    show (15 + 4 * (2 * l + 1) - 15) % 8 = 4 by omega, show (2 * l + 1) / 2 = l by omega,
    show (2 * l + 1) % 2 = 1 by omega, ↓reduceIte]

theorem assignment_read_high {i : Nat} (hi : i < 12) :
    x.assignment (p := p) (16 + 4 * i) = ((x.read (i / 2) (2 * (i % 2) + 1) : Nat) : ZMod p) := by
  obtain ⟨l, h, small, rfl⟩ : ∃ l h, h < 2 ∧ i = 2 * l + h :=
    ⟨i / 2, i % 2, Nat.mod_lt _ (by decide), by omega⟩
  interval_cases h <;>
  simp only [RowInput.assignment, RowInput.column, RowInput.lanePort, show ¬16 + 4 * (2 * l + 0) < 15 by omega,
    show 16 + 4 * (2 * l + 0) < 63 by omega, show (16 + 4 * (2 * l + 0) - 15) / 8 = l by omega,
    show (16 + 4 * (2 * l + 0) - 15) % 8 = 1 by omega, show (2 * l + 0) / 2 = l by omega,
    show (2 * l + 0) % 2 = 0 by omega, show ¬16 + 4 * (2 * l + 1) < 15 by omega,
    show 16 + 4 * (2 * l + 1) < 63 by omega, show (16 + 4 * (2 * l + 1) - 15) / 8 = l by omega,
    show (16 + 4 * (2 * l + 1) - 15) % 8 = 5 by omega, show (2 * l + 1) / 2 = l by omega,
    show (2 * l + 1) % 2 = 1 by omega, ↓reduceIte]

theorem assignment_written_low {i : Nat} (hi : i < 12) :
    x.assignment (p := p) (17 + 4 * i) = ((x.written (i / 2) (2 * (i % 2)) : Nat) : ZMod p) := by
  obtain ⟨l, h, small, rfl⟩ : ∃ l h, h < 2 ∧ i = 2 * l + h :=
    ⟨i / 2, i % 2, Nat.mod_lt _ (by decide), by omega⟩
  interval_cases h <;>
  simp only [RowInput.assignment, RowInput.column, RowInput.lanePort, show ¬17 + 4 * (2 * l + 0) < 15 by omega,
    show 17 + 4 * (2 * l + 0) < 63 by omega, show (17 + 4 * (2 * l + 0) - 15) / 8 = l by omega,
    show (17 + 4 * (2 * l + 0) - 15) % 8 = 2 by omega, show (2 * l + 0) / 2 = l by omega,
    show (2 * l + 0) % 2 = 0 by omega, show ¬17 + 4 * (2 * l + 1) < 15 by omega,
    show 17 + 4 * (2 * l + 1) < 63 by omega, show (17 + 4 * (2 * l + 1) - 15) / 8 = l by omega,
    show (17 + 4 * (2 * l + 1) - 15) % 8 = 6 by omega, show (2 * l + 1) / 2 = l by omega,
    show (2 * l + 1) % 2 = 1 by omega, ↓reduceIte]

theorem assignment_written_high {i : Nat} (hi : i < 12) :
    x.assignment (p := p) (18 + 4 * i) = ((x.written (i / 2) (2 * (i % 2) + 1) : Nat) : ZMod p) := by
  obtain ⟨l, h, small, rfl⟩ : ∃ l h, h < 2 ∧ i = 2 * l + h :=
    ⟨i / 2, i % 2, Nat.mod_lt _ (by decide), by omega⟩
  interval_cases h <;>
  simp only [RowInput.assignment, RowInput.column, RowInput.lanePort, show ¬18 + 4 * (2 * l + 0) < 15 by omega,
    show 18 + 4 * (2 * l + 0) < 63 by omega, show (18 + 4 * (2 * l + 0) - 15) / 8 = l by omega,
    show (18 + 4 * (2 * l + 0) - 15) % 8 = 3 by omega, show (2 * l + 0) / 2 = l by omega,
    show (2 * l + 0) % 2 = 0 by omega, show ¬18 + 4 * (2 * l + 1) < 15 by omega,
    show 18 + 4 * (2 * l + 1) < 63 by omega, show (18 + 4 * (2 * l + 1) - 15) / 8 = l by omega,
    show (18 + 4 * (2 * l + 1) - 15) % 8 = 7 by omega, show (2 * l + 1) / 2 = l by omega,
    show (2 * l + 1) % 2 = 1 by omega, ↓reduceIte]

/-- The lane index column of lane `l`. -/
theorem assignment_index {l : Nat} (hl : l < 6) :
    x.assignment (p := p) (7 + l) = ((x.indices[l] : Nat) : ZMod p) := by
  interval_cases l <;> rfl

end RowInput

/-- A RAM word of the state block: its address limbs are the pointer's, the offset added to the low limb. -/
theorem ramCell_code {o : Nat} (small : o < 62) : (ramCell o).addressCode = Nat.pair 1 (Nat.pair (4 * o) 64) := by
  simp only [ramCell, Cell.addressCode, Word.ofBitVec, stateBase, Word.value, limbBase, BitVec.toNat_ofNat]
  congr 2 <;> omega

end Airbender.NonVacuous.KeccakSpan
