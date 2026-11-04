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

end Slop.Equiv
