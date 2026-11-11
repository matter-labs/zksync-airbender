module
public import Human.Helpers.Delegation.RVDecoder
public import Slop.KernelRfl

@[expose] public section

/-! The caller program of the hash-span caller witnesses: `n` copies of `csrrw x0, 0x7C8, x0` (the Blake2s G
    delegation, `0x7C801073`) at the aligned ROM addresses `first, first + 4, …`. The ROM below `first` holds a
    concrete prefix (an ordinary preparation instruction, or nothing); from `first` on every byte is the caller
    instruction's byte at its address modulo four. The program image is built by one lemma over the address list
    (`image_map`) and one ROM read per address (`read_caller`), never by evaluating the 56 entries. -/

namespace Airbender.NonVacuous.HashCallers
open Trace

/-- `csrrw x0, 0x7C8, x0`. -/
def callerBits : BitVec 32 := 0x7C801073#32

/-- The caller instruction's byte at a ROM address `≡ i (mod 4)`. -/
def callerByte (i : Nat) : BitVec 8 := callerBits.extractLsb' (8 * (i % 4)) 8

/-- The ROM: `prefixBytes` below `first`, the caller instruction from `first` on. -/
def rom (first : Nat) (prefixBytes : Nat → BitVec 8) (address : BitVec 32) : BitVec 8 :=
  if address.toNat < first then prefixBytes address.toNat else callerByte address.toNat

/-- The caller entry at `pc` (the G family, both GPR operands x0). -/
def callerEntry (pc : BitVec 32) : Delegation.Caller.RVProgramEntry := ⟨pc, callerBits, ⟨.blakeG, 0, 0, 0, ⟨0, 0⟩, 128, 0⟩⟩

/-- The caller addresses `first + 4 k`, `k < n`. -/
def callerPCs (first n : Nat) : List (BitVec 32) := (List.range n).map fun k => BitVec.ofNat 32 (first + 4 * k)

def program (first n : Nat) : List Delegation.Caller.RVProgramEntry := (callerPCs first n).map callerEntry

/-- An image whose every address gives its entry. -/
theorem image_map {Kind : Type} {projection : RV.Instr → Option (DecoderData Kind)} {before : RV.State}
    {addresses : List (BitVec 32)} {entry : BitVec 32 → RVProgramEntry Kind}
    (each : ∀ a ∈ addresses, rvProgramEntryWith projection before a = some (entry a)) :
    rvProgramImageWith projection before addresses = some (addresses.map entry) := by
  induction addresses with
  | nil => rfl
  | cons a rest ih =>
    simp only [rvProgramImageWith, List.mapM_cons, each a (List.mem_cons_self ..), List.map_cons] at ih ⊢
    rw [ih fun b member => each b (List.mem_cons_of_mem _ member)]
    rfl

theorem succ_toNat (a : BitVec 32) (h : a.toNat + 1 < 2 ^ 32) : (a + 1).toNat = a.toNat + 1 := by
  rw [BitVec.toNat_add]
  simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.one_mod]
  omega

theorem decode_caller : RV.decode callerBits = some (.delegate .blakeG) := by kernel_rfl

/-- An aligned ROM word at or after `first` reads the caller instruction. -/
theorem read_caller {first : Nat} {prefixBytes : Nat → BitVec 8} {m : Nat} (after : first ≤ 4 * m)
    (room : 4 * m + 4 ≤ 2 ^ 32) : RV.read (rom first prefixBytes) (BitVec.ofNat 32 (4 * m)) 4 = callerBits := by
  have byte (i : Nat) (small : i < 4) (a : BitVec 32) (value : a.toNat = 4 * m + i) :
      rom first prefixBytes a = callerByte i := by
    rw [rom, value, ite_eq_right (by omega), callerByte, callerByte,
      show (4 * m + i) % 4 = i % 4 by omega]
  simp only [RV.read]
  have zero : (BitVec.ofNat 32 (4 * m)).toNat = 4 * m := by rw [BitVec.toNat_ofNat]; omega
  have one := succ_toNat _ (by omega : (BitVec.ofNat 32 (4 * m)).toNat + 1 < 2 ^ 32)
  have two := succ_toNat _ (by omega : (BitVec.ofNat 32 (4 * m) + 1).toNat + 1 < 2 ^ 32)
  have three := succ_toNat _ (by omega : (BitVec.ofNat 32 (4 * m) + 1 + 1).toNat + 1 < 2 ^ 32)
  rw [byte 0 (by omega) _ zero, byte 1 (by omega) _ (by omega), byte 2 (by omega) _ (by omega),
    byte 3 (by omega) _ (by omega)]
  decide

/-- The caller program is the image of its addresses. -/
theorem program_image {before : RV.State} {first n : Nat} {prefixBytes : Nat → BitVec 8}
    (memory : before.rom = rom first prefixBytes) (aligned : first % 4 = 0) (inside : first + 4 * n ≤ RV.ROM_END) :
    Delegation.Caller.rvProgramImage before (callerPCs first n) = some (program first n) := by
  refine image_map fun a member => ?_
  obtain ⟨k, present, rfl⟩ := List.mem_map.mp member
  have small := List.mem_range.mp present
  have bound : first + 4 * k < 2 ^ 32 := by simp only [RV.ROM_END] at inside; omega
  have value : (BitVec.ofNat 32 (first + 4 * k)).toNat = first + 4 * k := by
    rw [BitVec.toNat_ofNat]; omega
  have word : BitVec.ofNat 32 (first + 4 * k) = BitVec.ofNat 32 (4 * (first / 4 + k)) := by congr 1; omega
  simp only [rvProgramEntryWith, value]
  rw [ite_eq_right (by simp only [RV.ROM_END] at inside ⊢; omega), memory, word,
    read_caller (by omega) (by omega), decode_caller, ← word]
  rfl

end Airbender.NonVacuous.HashCallers
