import Airbender.Proofs.Sail.PC
import Mathlib.Tactic.IntervalCases

namespace Airbender.Reference.RiscV.Sail
open Airbender.Reference.Sail
open _root_.Sail.ArchSem

variable [MemoryPlatform SailRV32.exception]

omit [MemoryPlatform SailRV32.exception] in
theorem extend_word (unsigned : Bool) (value : BitVec 32) :
    SailRV32.Functions.extend_value unsigned value = value := by
  cases unsigned <;> simp [SailRV32.Functions.extend_value,
    SailRV32.Functions.sign_extend, SailRV32.Functions.zero_extend,
    _root_.Sail.BitVec.signExtend, _root_.Sail.BitVec.zeroExtend]

/-- One execution lemma for every supported load width and extension mode. -/
theorem load {before : State} {imm : BitVec 12} {rs1 rd : SailRV32.regidx}
    {width : Nat} (small : width ≤ 4) (unsigned : Bool) {value : BitVec (8 * width)}
    (read : run (SailRV32.Functions.vmem_read rs1
      (SailRV32.Functions.sign_extend (m := 32) imm) width (.Load .Data) false false false) before =
        .ok (.Ok value) before) :
    run (SailRV32.Functions.execute_LOAD imm rs1 rd unsigned width) before =
      run (do
        SailRV32.Functions.wX_bits rd (SailRV32.Functions.extend_value unsigned value)
        pure SailRV32.Functions.RETIRE_SUCCESS) before := by
  have bound : decide (width ≤ SailRV32.Functions.xlen_bytes) = true := by
    simpa [SailRV32.Functions.xlen_bytes] using small
  have assertion (message : String) : SailRV32.assert true message = (pure () : SailRV32.SailM Unit) := rfl
  simp only [SailRV32.Functions.execute_LOAD, bound]
  rw [assertion, freeM_pure_bind, run_bind_of_ok _ _ _ _ _ read]

/-- LW reuses the same clause proof, with extension reducing to the identity. -/
theorem load_word {before : State} {imm : BitVec 12} {rs1 rd : SailRV32.regidx}
    {value : BitVec 32}
    (read : run (SailRV32.Functions.vmem_read rs1
      (SailRV32.Functions.sign_extend (m := 32) imm) 4 (.Load .Data) false false false) before =
        .ok (.Ok value) before) :
    run (SailRV32.Functions.execute_LOAD imm rs1 rd false 4) before =
      run (do SailRV32.Functions.wX_bits rd value; pure SailRV32.Functions.RETIRE_SUCCESS) before := by
  have result := load (rd := rd) (by decide) false read
  simpa only [extend_word] using result

/-- The original SW clause reads rs2 and performs a native memory access. -/
theorem store_word {before after : State} {imm : BitVec 12} {rs1 rs2 : SailRV32.regidx}
    {value : BitVec 32}
    (read : run (SailRV32.Functions.rX_bits rs2) before = .ok value before)
    (write : run (SailRV32.Functions.vmem_write rs1
      (SailRV32.Functions.sign_extend (m := 32) imm) 4 value (.Store .Data) false false false) before =
        .ok (.Ok true) after) :
    run (SailRV32.Functions.execute_STORE imm rs2 rs1 4) before =
      .ok SailRV32.Functions.RETIRE_SUCCESS after := by
  change run (SailRV32.Functions.rX_bits rs2 >>= fun data =>
    SailRV32.Functions.vmem_write rs1 (SailRV32.Functions.sign_extend (m := 32) imm) 4
      (_root_.Sail.BitVec.extractLsb data 31 0) (.Store .Data) false false false >>= fun result =>
      match result with
      | .Ok _ => pure SailRV32.Functions.RETIRE_SUCCESS
      | .Err error => pure error) before = _
  rw [run_bind_of_ok _ _ _ _ _ read]
  have extract (v : BitVec 32) : _root_.Sail.BitVec.extractLsb v 31 0 = v := by
    simp [_root_.Sail.BitVec.extractLsb, BitVec.extractLsb]
  simp only [extract]
  rw [run_bind_of_ok _ _ _ _ _ write]
  rfl

omit [MemoryPlatform SailRV32.exception] in
/-- Native writes of up to four bytes preserve registers. -/
theorem write_memory_frame {size : Nat} (small : size ≤ 4)
    (address : BitVec 32) (value : BitVec (8 * size)) (before : State) :
    ∃ after, run (writeMemory (size := size) address value) before = .ok () after ∧
      after.regs = before.regs := by
  interval_cases size <;> exact ⟨_, rfl, rfl⟩

omit [MemoryPlatform SailRV32.exception] in
theorem write_word_frame (address : BitVec 32) (value : BitVec 32) (before : State) :
    ∃ after, run (writeMemory (size := 4) address value) before = .ok () after ∧
      after.regs = before.regs :=
  write_memory_frame (size := 4) (by decide) address value before

omit [MemoryPlatform SailRV32.exception] in
private theorem toNat_byte_append {n : Nat} (hi : BitVec n) (lo : BitVec 8) :
    (hi ++ lo).toNat = hi.toNat * 256 + lo.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt lo.isLt, Nat.shiftLeft_eq]

set_option maxRecDepth 2048 in
omit [MemoryPlatform SailRV32.exception] in
/-- A successful native word read supplies every byte and aligned halfword read.
    Extraction uses the pinned sequential interpreter, not a memory assumption. -/
theorem read_subword {before : State} {addr : Nat} {word : BitVec 32} (byte : Bool) {offset : Nat}
    (bound : offset < 4) (aligned : byte = false → offset % 2 = 0)
    (h : readBytes (ue := SailRV32.exception) 4 addr before = .ok word before) :
    (readBytes (ue := SailRV32.exception) (if byte then 1 else 2) (addr + offset)).run before =
      .ok ((word >>> (8 * offset)).setWidth (8 * (if byte then 1 else 2))) before := by
  simp only [readBytes, readByte, get, getThe, MonadStateOf.get, bind, pure,
    EStateM.bind, EStateM.get, EStateM.pure] at h
  cases first : before.mem[addr]?
  · simp [throw, throwThe, MonadExceptOf.throw, EStateM.throw, first] at h
  · rename_i a
    cases second : before.mem[addr + 1]?
    · simp [EStateM.pure, throw, throwThe, MonadExceptOf.throw, EStateM.throw, first, second] at h
    · rename_i b
      cases third : before.mem[addr + 2]?
      · simp [EStateM.pure, throw, throwThe, MonadExceptOf.throw, EStateM.throw, first, second, third, Nat.add_assoc] at h
      · rename_i c
        cases fourth : before.mem[addr + 3]?
        · simp [EStateM.pure, throw, throwThe, MonadExceptOf.throw, EStateM.throw, first, second, third, fourth, Nat.add_assoc] at h
        · rename_i d
          simp [EStateM.pure, first, second, third, fourth, Nat.add_assoc] at h
          subst word
          cases byte <;> interval_cases offset
          all_goals solve
            | (have := aligned rfl; norm_num at this)
            | (simp [EStateM.run, readBytes, readByte, get, getThe, MonadStateOf.get, bind, pure,
                 EStateM.bind, EStateM.get, EStateM.pure, first, second, third, fourth, Nat.add_assoc]
               apply BitVec.eq_of_toNat_eq
               simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
                 toNat_byte_append]
               norm_num only [Nat.reducePow, Nat.shiftRight_eq_div_pow, Nat.reduceMul,
                 Nat.reduceAdd, Nat.div_one]
               omega)

set_option maxRecDepth 2048 in
theorem store_subword {before after : State} {imm : BitVec 12} {rs1 rs2 : SailRV32.regidx}
    (byte : Bool) {value : BitVec 32}
    (read : run (SailRV32.Functions.rX_bits rs2) before = .ok value before)
    (write : run (SailRV32.Functions.vmem_write rs1
      (SailRV32.Functions.sign_extend (m := 32) imm) (if byte then 1 else 2)
      (value.setWidth (8 * (if byte then 1 else 2))) (.Store .Data) false false false) before =
      .ok (.Ok true) after) :
    run (SailRV32.Functions.execute_STORE imm rs2 rs1 (if byte then 1 else 2)) before =
      .ok SailRV32.Functions.RETIRE_SUCCESS after := by
  cases byte
  · change run (SailRV32.Functions.vmem_write rs1 (SailRV32.Functions.sign_extend (m := 32) imm) 2
      (value.setWidth 16) (.Store .Data) false false false) before = .ok (.Ok true) after at write
    change run (SailRV32.Functions.rX_bits rs2 >>= fun data =>
      SailRV32.Functions.vmem_write rs1 (SailRV32.Functions.sign_extend (m := 32) imm) 2
        (_root_.Sail.BitVec.extractLsb data 15 0) (.Store .Data) false false false >>= fun result =>
        match result with | .Ok _ => pure SailRV32.Functions.RETIRE_SUCCESS | .Err error => pure error) before = _
    rw [run_bind_of_ok _ _ _ _ _ read]
    have extracted : _root_.Sail.BitVec.extractLsb value 15 0 = value.setWidth 16 := by
      apply BitVec.eq_of_toNat_eq
      simp [_root_.Sail.BitVec.extractLsb, BitVec.extractLsb, Nat.shiftRight_eq_div_pow]
    rw [extracted, run_bind_of_ok _ _ _ _ _ write]
    rfl
  · change run (SailRV32.Functions.vmem_write rs1 (SailRV32.Functions.sign_extend (m := 32) imm) 1
      (value.setWidth 8) (.Store .Data) false false false) before = .ok (.Ok true) after at write
    change run (SailRV32.Functions.rX_bits rs2 >>= fun data =>
      SailRV32.Functions.vmem_write rs1 (SailRV32.Functions.sign_extend (m := 32) imm) 1
        (_root_.Sail.BitVec.extractLsb data 7 0) (.Store .Data) false false false >>= fun result =>
        match result with | .Ok _ => pure SailRV32.Functions.RETIRE_SUCCESS | .Err error => pure error) before = _
    rw [run_bind_of_ok _ _ _ _ _ read]
    have extracted : _root_.Sail.BitVec.extractLsb value 7 0 = value.setWidth 8 := by
      apply BitVec.eq_of_toNat_eq
      simp [_root_.Sail.BitVec.extractLsb, BitVec.extractLsb, Nat.shiftRight_eq_div_pow]
    rw [extracted, run_bind_of_ok _ _ _ _ _ write]
    rfl

end Airbender.Reference.RiscV.Sail
