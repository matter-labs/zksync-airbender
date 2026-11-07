import Airbender.Review.Helpers.Memory.ReducedMachineROMImage
import Airbender.Proofs.Sail.WordMemoryState

namespace Airbender.ReducedMachine.NativeROMProofs
open NativeROM Native Arithmetic Verification Trace Reference.RiscV.Sail
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- All eight words are read from the actual retained public column. -/
theorem fixture_words : fixture.words =
    [0x001080b3,0xfff08113,0x40208033,0x000071b7,0x00005217,0x0000a183,0x0020a023,0xc0001073] := by
  decide +kernel

/-- The finite public prefix bridge is a small exact kernel certificate. -/
theorem fixture_prefix (i : Fin 8) :
    fixture.word i.val = (wordMemoryROMWord i.val).toBitVec := by
  have all : ∀ j : Fin 8, fixture.word j.val = (wordMemoryROMWord j.val).toBitVec := by
    decide +kernel
  exact all i

/-- Exact retained fixture/padding bridge; no table-equivalence premise. -/
theorem fixture_word (index : Nat) :
    fixture.word index = (wordMemoryROMWord index).toBitVec := by
  by_cases inside : index < 8
  · exact fixture_prefix ⟨index,inside⟩
  · have length : fixture.words.length = 8 := by rw [fixture_words]; rfl
    have missing : fixture.words[index]? = none := List.getElem?_eq_none (by omega)
    have tail : NativeFixed.wordROMValue index = #v[4211,49152] := by
      unfold NativeFixed.wordROMValue
      split <;> first | rfl | omega
    simp only [WordROM.word,missing,Option.getD_none,wordMemoryROMWord,tail]
    exact (by decide +kernel : (0xc0001073 : BitVec 32) = (⟨4211,49152⟩ : Word).toBitVec)

/-- Symbolic finite-insert lookup; full four-MiB construction is not evaluated. -/
theorem byte_lookup (memory : Std.ExtHashMap Nat (BitVec 8)) (count key : Nat) :
    (byteMemory memory count)[key]? = if key < count then some (byte key) else memory[key]? := by
  induction count with
  | zero => simp [byteMemory]
  | succ count ih =>
    simp only [byteMemory,Std.ExtHashMap.getElem?_insert,ih]
    by_cases last : count = key
    · subst key; simp
    · simp only [beq_iff_eq,if_neg last]
      split_ifs <;> simp_all <;> omega

theorem state_byte (before : State) (key : Nat) :
    (state before).mem[key]? = if key < 4194304 then some (byte key) else before.mem[key]? :=
  byte_lookup before.mem 4194304 key

/-- Actual original little-endian word read at every aligned native ROM slot,
    including the entire repeated UNIMP tail. -/
theorem word_read (before : State) (i : Fin 1048576) :
    (Cell.ram (BitVec.ofNat 32 (4 * i.val))).read (state before) =
      .ok (fixture.word i.val) (state before) := by
  apply read_word_of_bytes
  have address : (BitVec.ofNat 32 (4 * i.val)).toNat = 4 * i.val := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have := i.isLt; omega)]
  intro j
  rw [address,state_byte,if_pos (by have := i.isLt; have := j.isLt; omega)]
  have quotient : (4 * i.val + j.val)/4 = i.val := by omega
  have remainder : (4 * i.val + j.val)%4 = j.val := by omega
  simp only [byte,quotient,remainder]

/-- Successful actual reads reconstruct the public extractor. This unchanged
    pure recursion is symbolic even for the complete ROM extent. -/
theorem read_rom_words_of_reads {before : State} {count : Nat} (value : Nat → BitVec 32)
    (reads : ∀ i : Fin count, (Cell.ram (BitVec.ofNat 32 (4 * i.val))).read before =
      .ok (value i.val) before) :
    readROMWords before count = some (Vector.ofFn fun i => value i.val) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    have earlier := ih (fun i => reads ⟨i.val, by omega⟩)
    have last := reads ⟨count, by omega⟩
    unfold readROMWords
    rw [earlier]
    simp only [bind, Option.bind, last, pure]
    congr 1
    ext i
    by_cases bound : i < count
    · simp [bound]
    · have final : i = count := by omega
      simp [final]



/-- The full original extractor returns the complete computed fixture/padding.
    No concrete million-word vector or byte map is evaluated in this proof. -/
theorem complete_image (before : State) :
    wordROMImage (state before) 1048576 = some complete := by
  have extracted : readROMWords (state before) 1048576 =
      some (Vector.ofFn fun i : Fin 1048576 => fixture.word i.val) :=
    read_rom_words_of_reads (fun index => fixture.word index) (fun i => word_read before i)
  unfold wordROMImage
  rw [dif_pos (by decide),extracted]
  rfl

theorem memory_update_registers (before : State) (memory : Std.ExtHashMap Nat (BitVec 8)) :
    ({ before with mem := memory } : State).regs = before.regs := rfl

theorem registers (before : State) : (state before).regs = before.regs :=
  memory_update_registers before (byteMemory before.mem 4194304)

theorem outside_byte (before : State) {key : Nat} (outside : 4194304 ≤ key) :
    (state before).mem[key]? = before.mem[key]? := by
  rw [state_byte,if_neg (by omega)]

/-- The actual numerical ROM references have original Sail byte reads in the
    constructed state, independently of ignored native shadow seed values. -/
theorem numerical_read (before : State) (i : Fin 1048576) :
    (Cell.ram (BitVec.ofNat 32 (4 * i.val))).read (state before) =
      .ok (wordMemoryROMWord i.val).toBitVec (state before) := by
  rw [← fixture_word]
  exact word_read before i

end Airbender.ReducedMachine.NativeROMProofs
