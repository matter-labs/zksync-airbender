import Slop.Sail.PC
import Slop.Sail.ResetState
import Slop.Sail.WordMemoryState
import Human.ISA.State
import Human.Helpers.Memory.InitialImage

/-! `toSail s cells : Reference.RiscV.Sail.State`: the hash-map Sail state that an `RV.State` stands for on the
circuit's side. Registers: PC and x1..x31 from `s`, every other register at its reset value. Memory: the ROM bytes
`[0, RV.ROM_END)` and the four bytes of each RAM cell, from `s.mem`; other bytes are absent. Built by folds of
inserts whose value depends only on the key, so overlaps are harmless and no disjointness is needed.

Proven here: `Configured (toSail s cells)`, the register reads (`Cell.read` of a register cell gives `s.getReg`),
and the word reads (`Cell.read` of a RAM cell, or of a ROM word, gives `RV.read s.mem a 4`). -/

namespace Slop.Equiv

open Airbender.Reference.RiscV.Sail

/-- The register values `toSail` sets: PC and x1..x31 from `s`; every other register at its reset value. -/
noncomputable def rvRegVal (s : RV.State) : (r : SailRV32.Register) → SailRV32.RegisterType r := fun r =>
  match r with
  | .PC => s.pc
  | .x1 => s.getReg 1 | .x2 => s.getReg 2 | .x3 => s.getReg 3 | .x4 => s.getReg 4
  | .x5 => s.getReg 5 | .x6 => s.getReg 6 | .x7 => s.getReg 7 | .x8 => s.getReg 8
  | .x9 => s.getReg 9 | .x10 => s.getReg 10 | .x11 => s.getReg 11 | .x12 => s.getReg 12
  | .x13 => s.getReg 13 | .x14 => s.getReg 14 | .x15 => s.getReg 15 | .x16 => s.getReg 16
  | .x17 => s.getReg 17 | .x18 => s.getReg 18 | .x19 => s.getReg 19 | .x20 => s.getReg 20
  | .x21 => s.getReg 21 | .x22 => s.getReg 22 | .x23 => s.getReg 23 | .x24 => s.getReg 24
  | .x25 => s.getReg 25 | .x26 => s.getReg 26 | .x27 => s.getReg 27 | .x28 => s.getReg 28
  | .x29 => s.getReg 29 | .x30 => s.getReg 30 | .x31 => s.getReg 31
  | r => Configuration.resetState.regs r

/-- The registers a program can change, as `toSail` sets them. -/
def rvWrittenRegs : List SailRV32.Register :=
  [.PC, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x18,
    .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31]

/-- Byte addresses a RAM cell occupies (four bytes, little-endian). -/
def cellBytes : Airbender.Trace.Cell → List Nat
  | .register _ => []
  | .ram a => [a.toNat, a.toNat + 1, a.toNat + 2, a.toNat + 3]

/-- Memory addresses `toSail` sets: the ROM and the bytes of the tracked RAM cells. -/
@[irreducible] def rvMemKeys (cells : List Airbender.Trace.Cell) : List Nat :=
  List.range RV.ROM_END ++ cells.flatMap cellBytes

/-- Registers of `toSail`: the reset registers with `rvWrittenRegs` overwritten from `s`. -/
@[irreducible] noncomputable def rvRegs (s : RV.State) : Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType :=
  rvWrittenRegs.foldl (fun m r => m.insert r (rvRegVal s r)) resetMachine.regs

/-- Memory of `toSail`: each key of `rvMemKeys` holds the byte of `s.mem` at that address. -/
@[irreducible] noncomputable def rvMem (s : RV.State) (cells : List Airbender.Trace.Cell) : Std.ExtHashMap Nat (BitVec 8) :=
  (rvMemKeys cells).foldl (fun m a => m.insert a (s.mem (BitVec.ofNat 32 a))) ∅

/-- The Sail state an `RV.State` and a list of tracked cells stand for (hash maps; see the module comment). -/
noncomputable def toSail (s : RV.State) (cells : List Airbender.Trace.Cell) : Airbender.Reference.RiscV.Sail.State :=
  { resetMachine with regs := rvRegs s, mem := rvMem s cells }

/-! ### Folds over hash maps -/

theorem rvRegs_get (s : RV.State) : ∀ (l : List SailRV32.Register) (m : Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType)
    (r : SailRV32.Register),
    (l.foldl (fun m r => m.insert r (rvRegVal s r)) m).get? r =
      if r ∈ l then some (rvRegVal s r) else m.get? r
  | [], m, r => by simp
  | n :: rest, m, r => by
    rw [List.foldl_cons, rvRegs_get s rest _ r]
    by_cases hr : r = n
    · subst hr
      simp [Std.ExtDHashMap.get?_insert]
    · by_cases hin : r ∈ rest
      · simp [hin, hr]
      · simp [hin, hr, Std.ExtDHashMap.get?_insert, Ne.symm hr]

theorem rvMem_get (s : RV.State) : ∀ (l : List Nat)
    (m : Std.ExtHashMap Nat (BitVec 8)) (a : Nat),
    (l.foldl (fun m a => m.insert a (s.mem (BitVec.ofNat 32 a))) m)[a]? =
      if a ∈ l then some (s.mem (BitVec.ofNat 32 a)) else m[a]?
  | [], m, a => by simp
  | n :: rest, m, a => by
    rw [List.foldl_cons, rvMem_get s rest _ a]
    by_cases ha : a = n
    · subst ha
      simp [Std.ExtHashMap.getElem?_insert]
    · by_cases hin : a ∈ rest
      · simp [hin, ha]
      · simp [hin, ha, Std.ExtHashMap.getElem?_insert, Ne.symm ha]

theorem toSail_mem_eq (s : RV.State) (cells : List Airbender.Trace.Cell) : (toSail s cells).mem = rvMem s cells := by unfold toSail; rfl

theorem toSail_regs_eq (s : RV.State) (cells : List Airbender.Trace.Cell) : (toSail s cells).regs = rvRegs s := by unfold toSail; rfl

/-- The memory of `toSail` at a key of `rvMemKeys`. -/
theorem toSail_mem_get (s : RV.State) (cells : List Airbender.Trace.Cell) (a : Nat) (h : a ∈ rvMemKeys cells) :
    (toSail s cells).mem[a]? = some (s.mem (BitVec.ofNat 32 a)) := by
  rw [toSail_mem_eq]
  unfold rvMem
  rw [rvMem_get, if_pos h]

theorem toSail_regs_get (s : RV.State) (cells : List Airbender.Trace.Cell) (r : SailRV32.Register) :
    (toSail s cells).regs.get? r = if r ∈ rvWrittenRegs then some (rvRegVal s r) else resetMachine.regs.get? r := by
  rw [toSail_regs_eq]
  unfold rvRegs
  rw [rvRegs_get]

/-! ### Configured and the register reads -/

theorem rvWritten_sub (r : SailRV32.Register) (h : r ∈ rvWrittenRegs) : Configuration.writtenByProgram r = true := by
  cases r <;> simp_all [rvWrittenRegs, Configuration.writtenByProgram]

theorem configured_toSail (s : RV.State) (cells : List Airbender.Trace.Cell) :
    Airbender.Reference.RiscV.Sail.Configured (toSail s cells) := by
  intro r hr
  rw [toSail_regs_get, if_neg (fun h => by have := rvWritten_sub r h; simp [hr] at this), reset_machine_get]

theorem toSail_pc (s : RV.State) (cells : List Airbender.Trace.Cell) :
    (toSail s cells).regs.get? .PC = some s.pc := by
  rw [toSail_regs_get, if_pos (by simp [rvWrittenRegs])]
  rfl

open Airbender.Reference.Sail _root_.Sail.ArchSem

/-! ### Word reads of `RV.read`, bit by bit -/

theorem byte_getLsbD_ge (x : BitVec 8) (j : Nat) (hj : 8 ≤ j) : x.getLsbD j = false := by
  simp only [BitVec.getLsbD]
  exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by norm_num) hj))

/-- Bit `j` (for `j < 32`) of `RV.read m a n` is bit `j % 8` of the byte at `a + j / 8`, when `j < 8 n`. -/
theorem read_getLsbD (m : RV.Word → BitVec 8) (n : Nat) : ∀ (a : RV.Word) (j : Nat), j < 32 →
    (RV.read m a n).getLsbD j = (decide (j < 8 * n) && (m (a + BitVec.ofNat 32 (j / 8))).getLsbD (j % 8)) := by
  induction n with
  | zero => intro a j _; simp [RV.read]
  | succ n ih =>
    intro a j hj
    simp only [RV.read, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
    by_cases h8 : j < 8
    · have h0 : j / 8 = 0 := by omega
      have h1 : j % 8 = j := by omega
      have h2 : j < 8 * (n + 1) := by omega
      simp [h0, h1, h8, h2, hj]
    · have hr := ih (a + 1) (j - 8) (by omega)
      have hq : j / 8 = (j - 8) / 8 + 1 := by omega
      have hq' : a + BitVec.ofNat 32 (j / 8) = a + 1 + BitVec.ofNat 32 ((j - 8) / 8) := by
        rw [hq, BitVec.ofNat_add]; bv_omega
      have hm : j % 8 = (j - 8) % 8 := by omega
      have hA : (m a).getLsbD j = false := byte_getLsbD_ge _ _ (by omega)
      have hb : (j - 8 < 8 * n) = (j < 8 * (n + 1)) := propext (by omega)
      rw [hq', hm, hr]
      simp [hA, hb, h8, hj]

/-- Byte `k` of a word read is the byte of memory at `a + k`. -/
theorem rv_read_byte (m : RV.Word → BitVec 8) (a : RV.Word) (k : Nat) (hk : k < 4) :
    (RV.read m a 4).extractLsb' (8 * k) 8 = m (a + BitVec.ofNat 32 k) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_extractLsb', read_getLsbD _ _ _ _ (by omega)]
  by_cases hj8 : j < 8
  · have e1 : 8 * k + j < 32 := by omega
    have e2 : (8 * k + j) / 8 = k := by omega
    have e3 : (8 * k + j) % 8 = j := by omega
    simp [hj8, e1, e2, e3]
  · simp [hj8, byte_getLsbD_ge _ _ (show 8 ≤ j by omega)]

/-! ### Register and word reads of `toSail` -/

theorem readReg_toSail (s : RV.State) (cells : List Airbender.Trace.Cell) (reg : SailRV32.Register)
    (h : reg ∈ rvWrittenRegs) :
    run (SailRV32.readReg reg) (toSail s cells) = .ok (rvRegVal s reg) (toSail s cells) := by
  apply read_register
  rw [toSail_regs_get, ite_eq_left_iff.mpr (fun hn => absurd h hn)]

/-- The generic register read of `toSail` gives `s.getReg i` (x0 is 0). -/
theorem rX_toSail (s : RV.State) (cells : List Airbender.Trace.Cell) (i : BitVec 5) :
    run (SailRV32.Functions.rX_bits (.Regidx i)) (toSail s cells) = .ok (s.getReg i) (toSail s cells) := by
  obtain ⟨⟨n, hn⟩⟩ := i
  have bound : n < 32 := hn
  simp only [SailRV32.Functions.rX_bits, SailRV32.Functions.rX]
  interval_cases n
  all_goals first
    | rfl
    | (refine (run_bind_of_ok _ _ _ _ _ (readReg_toSail s cells _ ?_)).trans ?_
       · simp [rvWrittenRegs]
       · rfl)

/-- A four-byte read of `toSail` at `a` gives `RV.read s.mem a 4`, when every byte it reads is set. -/
theorem readBytes_toSail (s : RV.State) (cells : List Airbender.Trace.Cell) (a : RV.Word)
    (keys : ∀ i : Fin 4, a.toNat + i.val ∈ rvMemKeys cells) :
    (readBytes (ue := SailRV32.exception) 4 a.toNat).run (toSail s cells) =
      .ok (RV.read s.mem a 4) (toSail s cells) := by
  apply read_word_of_bytes
  intro i
  rw [toSail_mem_get s cells _ (keys i), rv_read_byte s.mem a i.val i.isLt, BitVec.ofNat_add, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]

theorem ram_keys (cells : List Airbender.Trace.Cell) (a : BitVec 32) (h : Airbender.Trace.Cell.ram a ∈ cells)
    (i : Fin 4) : a.toNat + i.val ∈ rvMemKeys cells := by
  obtain ⟨i, hi⟩ := i
  unfold rvMemKeys
  refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨.ram a, h, ?_⟩))
  interval_cases i <;> simp [cellBytes]

theorem rom_keys (cells : List Airbender.Trace.Cell) (a : BitVec 32) (h : a.toNat + 4 ≤ RV.ROM_END)
    (i : Fin 4) : a.toNat + i.val ∈ rvMemKeys cells := by
  have := i.isLt
  unfold rvMemKeys
  exact List.mem_append.mpr (Or.inl (List.mem_range.mpr (by omega)))

/-- `Cell.read` of a register cell of `toSail`. -/
theorem cell_read_register (s : RV.State) (cells : List Airbender.Trace.Cell) (i : BitVec 5) :
    (Airbender.Trace.Cell.register i).read (toSail s cells) = .ok (s.getReg i) (toSail s cells) :=
  rX_toSail s cells i

/-- `Cell.read` of a tracked RAM cell of `toSail`. -/
theorem cell_read_ram (s : RV.State) (cells : List Airbender.Trace.Cell) (a : BitVec 32)
    (h : Airbender.Trace.Cell.ram a ∈ cells) :
    (Airbender.Trace.Cell.ram a).read (toSail s cells) = .ok (RV.read s.mem a 4) (toSail s cells) :=
  readBytes_toSail s cells a (ram_keys cells a h)

/-- A four-byte read of `toSail` inside the ROM. -/
theorem rom_read (s : RV.State) (cells : List Airbender.Trace.Cell) (a : RV.Word)
    (h : a.toNat + 4 ≤ RV.ROM_END) :
    (readBytes (ue := SailRV32.exception) 4 a.toNat).run (toSail s cells) =
      .ok (RV.read s.mem a 4) (toSail s cells) :=
  readBytes_toSail s cells a (rom_keys cells a h)

end Slop.Equiv
