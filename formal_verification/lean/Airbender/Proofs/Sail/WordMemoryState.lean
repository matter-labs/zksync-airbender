import Airbender.Proofs.Sail.Memory
import Airbender.Proofs.Arithmetic.Bytes
import Mathlib.Tactic.FinCases

namespace Airbender.Reference.RiscV.Sail
open Airbender.Reference.Sail
open _root_.Sail.ArchSem

/-- The result of the pinned runtime's four byte inserts. This is an internal
    normal form for its effect, not an instruction specification. -/
def wordWriteState (before : State) (address : Nat) (value : BitVec 32) : State :=
  let m0 := before.mem.insert address (value.extractLsb' 0 8)
  let m1 := m0.insert (address + 1) (value.extractLsb' 8 8)
  let m2 := m1.insert (address + 2) (value.extractLsb' 16 8)
  { before with mem := m2.insert (address + 3) (value.extractLsb' 24 8) }

theorem write_word_state (before : State) (address : BitVec 32) (value : BitVec 32) :
    run (writeMemory (size := 4) address value) before =
      .ok () (wordWriteState before address.toNat value) := by
  have extended : (address.zeroExtend 34).toNat = address.toNat := by
    simp only [BitVec.zeroExtend, BitVec.toNat_setWidth]
    exact Nat.mod_eq_of_lt (by have bound := address.isLt; omega)
  change EStateM.run (do
    let _ ← (do
      pure PUnit.unit
      writeBytes (ue := SailRV32.exception) (n := 4) (address.zeroExtend 34).toNat value
      pure (Except.ok ()))
    pure ()) before = _
  simp [extended, wordWriteState, writeBytes, List.ofFn_succ, List.forM_cons, writeByte,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.run, EStateM.bind,
    EStateM.modifyGet, EStateM.pure, bind, pure]

/-- Reverse of `read_word_memory`: the actual byte entries determine the native
    little-endian word read. -/
theorem read_word_of_bytes {before : State} {address : Nat} {word : BitVec 32}
    (bytes : ∀ i : Fin 4, before.mem[address + i.val]? =
      some (word.extractLsb' (8 * i.val) 8)) :
    (readBytes (ue := SailRV32.exception) 4 address).run before = .ok word before := by
  have b0 : before.mem[address]? = some (word.extractLsb' 0 8) := bytes ⟨0, by decide⟩
  have b1 : before.mem[address + 1]? = some (word.extractLsb' 8 8) := bytes ⟨1, by decide⟩
  have b2 : before.mem[address + 2]? = some (word.extractLsb' 16 8) := bytes ⟨2, by decide⟩
  have b3 : before.mem[address + 3]? = some (word.extractLsb' 24 8) := bytes ⟨3, by decide⟩
  simp [readBytes, readByte, EStateM.run, get, getThe, MonadStateOf.get, bind, pure,
    EStateM.bind, EStateM.get, EStateM.pure, b0, b1, b2, b3, Nat.add_assoc]
  apply BitVec.eq_of_toNat_eq
  simp only [toNat_byte_append]
  have encoding := Airbender.Arithmetic.bytes_value word
  omega

theorem written_word_byte (before : State) (address : Nat) (value : BitVec 32) (i : Fin 4) :
    (wordWriteState before address value).mem[address + i.val]? =
      some (value.extractLsb' (8 * i.val) 8) := by
  fin_cases i <;> simp [wordWriteState, Std.ExtHashMap.getElem_insert]

theorem written_word_read (before : State) (address : Nat) (value : BitVec 32) :
    (readBytes (ue := SailRV32.exception) 4 address).run (wordWriteState before address value) =
      .ok value (wordWriteState before address value) :=
  read_word_of_bytes (written_word_byte before address value)

theorem read_word_frame {before after : State} (memory : after.mem = before.mem)
    {address : Nat} {value : BitVec 32}
    (read : (readBytes (ue := SailRV32.exception) 4 address).run before = .ok value before) :
    (readBytes (ue := SailRV32.exception) 4 address).run after = .ok value after := by
  apply read_word_of_bytes
  intro i
  rw [memory]
  exact read_word_memory read i

set_option backward.isDefEq.respectTransparency false in
/-- Register/control updates preserve successful reads at each supported width. -/
theorem read_memory_frame {size : Nat} (width : size = 1 ∨ size = 2 ∨ size = 4)
    {before after : State} (memory : after.mem = before.mem)
    {address : Nat} {value : BitVec (8 * size)}
    (read : (readBytes (ue := SailRV32.exception) size address).run before = .ok value before) :
    (readBytes (ue := SailRV32.exception) size address).run after = .ok value after := by
  rcases width with rfl | rfl | rfl
  · simp only [readBytes, readByte, get, getThe, MonadStateOf.get, bind, pure,
      EStateM.run, EStateM.bind, EStateM.get, EStateM.pure, memory] at read ⊢
    cases byte : before.mem[address]? <;> simp_all [EStateM.pure, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
  · simp only [readBytes, readByte, get, getThe, MonadStateOf.get, bind, pure,
      EStateM.run, EStateM.bind, EStateM.get, EStateM.pure, memory] at read ⊢
    cases first : before.mem[address]? <;> simp_all [EStateM.pure, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
    cases second : before.mem[address + 1]? <;> simp_all [EStateM.pure, EStateM.throw]
  · exact read_word_frame memory read

theorem rX_register_frame {before after : State} (registers : after.regs = before.regs)
    (index : BitVec 5) {value : BitVec 32}
    (read : run (SailRV32.Functions.rX_bits (.Regidx index)) before = .ok value before) :
    run (SailRV32.Functions.rX_bits (.Regidx index)) after = .ok value after := by
  have bound := index.isLt
  change run (SailRV32.Functions.rX (.Regno (index.toNat : Int))) before = _ at read
  change run (SailRV32.Functions.rX (.Regno (index.toNat : Int))) after = _
  interval_cases index.toNat
  all_goals first
    | (apply read_register
       rw [registers]
       exact read_register_iff.mp read)
    | (change EStateM.Result.ok (0 : BitVec 32) before = .ok value before at read
       rw [← (EStateM.Result.ok.inj read).1]
       rfl)

theorem gpr_write_memory (index : BitVec 5) (value : BitVec 32) (before : State) :
    ∃ after, run (SailRV32.Functions.wX_bits (.Regidx index) value) before = .ok () after ∧
      after.mem = before.mem := by
  have primitive (reg : SailRV32.Register) (v : SailRV32.RegisterType reg) :
      run (do SailRV32.writeReg reg v; pure ()) before =
        .ok () { before with regs := before.regs.insert reg v } := rfl
  have pureRun : run (pure () : SailRV32.SailM Unit) before = .ok () before := rfl
  have bound := index.isLt
  change ∃ after, run (SailRV32.Functions.wX (.Regno (index.toNat : Int)) value) before = _ ∧ _
  interval_cases index.toNat <;>
    simp [SailRV32.Functions.wX, SailRV32.Functions.regval_into_reg,
      write_callback_pure, freeM_pure_bind, primitive, pureRun]

theorem written_word_outside (before : State) (address : Nat) (value : BitVec 32)
    (key : Nat) (outside : key < address ∨ address + 4 ≤ key) :
    (wordWriteState before address value).mem[key]? = before.mem[key]? := by
  have k0 : key ≠ address := by omega
  have k1 : key ≠ address + 1 := by omega
  have k2 : key ≠ address + 2 := by omega
  have k3 : key ≠ address + 3 := by omega
  simp [wordWriteState, Std.ExtHashMap.getElem?_insert, Ne.symm k0, Ne.symm k1,
    Ne.symm k2, Ne.symm k3]

/-- A write preserves every other disjoint cell's actual read, including missing
    or nonzero byte entries outside its four-byte window. -/
theorem written_word_disjoint {before : State} (address : Nat) (value : BitVec 32)
    {other : Nat} {word : BitVec 32} (disjoint : other + 4 ≤ address ∨ address + 4 ≤ other)
    (read : (readBytes (ue := SailRV32.exception) 4 other).run before = .ok word before) :
    (readBytes (ue := SailRV32.exception) 4 other).run (wordWriteState before address value) =
      .ok word (wordWriteState before address value) := by
  apply read_word_of_bytes
  intro i
  have bound := i.isLt
  rw [written_word_outside before address value (other + i.val) (by omega)]
  exact read_word_memory read i

/-- Rewriting an already-present word with itself is a genuine Sail state frame. -/
theorem written_word_same {before : State} {address : Nat} {value : BitVec 32}
    (read : (readBytes (ue := SailRV32.exception) 4 address).run before = .ok value before) :
    wordWriteState before address value = before := by
  have bytes := read_word_memory read
  suffices memory : (wordWriteState before address value).mem = before.mem by
    cases before
    simp_all [wordWriteState]
  apply Std.ExtHashMap.ext_getElem?
  intro key
  by_cases inside : address ≤ key ∧ key < address + 4
  · let i : Fin 4 := ⟨key - address, by omega⟩
    have same : address + i.val = key := by dsimp [i]; omega
    rw [← same, written_word_byte, bytes i]
  · exact written_word_outside before address value key (by omega)

end Airbender.Reference.RiscV.Sail
