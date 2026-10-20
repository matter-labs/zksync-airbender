import Slop.Sail.PC

namespace Airbender.Reference.RiscV.Sail
open Airbender.Reference.Sail
open _root_.Sail.ArchSem

/-- Four-byte alignment discharges both native target-bit checks. -/
theorem aligned_access {target : BitVec 32} (aligned : target.toNat % 4 = 0) :
    _root_.Sail.BitVec.access target 0 = 0 ∧
    _root_.Sail.BitVec.access target 1 = 0 := by
  have low : target.toNat % 2 = 0 := by omega
  have second : target.toNat / 2 % 2 = 0 := by omega
  simp [_root_.Sail.BitVec.access, BitVec.getElem_eq_testBit_toNat,
    Nat.testBit, Nat.shiftRight_eq_div_pow, low, second]

/-- The native compressed-extension query is a read of misa, even for an
    aligned target. Its value is unrestricted; successful reading is required. -/
theorem compressed_query {state : State} {misa : BitVec 32}
    (read : run (SailRV32.readReg .misa) state = .ok misa state) :
    ∃ enabled, run (SailRV32.Functions.currentlyEnabled .Ext_Zca) state =
      .ok enabled state := by
  simp only [SailRV32.Functions.currentlyEnabled, SailRV32.Functions.hartSupports,
    freeM_bind_assoc, freeM_pure_bind]
  rw [run_bind_of_ok _ _ _ _ _ read]
  exact ⟨_, rfl⟩

/-- Aligned native jumps set nextPC and have no other state effect. -/
theorem jump_to_aligned {target : BitVec 32} {state : State} {misa : BitVec 32}
    (aligned : target.toNat % 4 = 0)
    (read : run (SailRV32.readReg .misa) state = .ok misa state) :
    run (SailRV32.Functions.jump_to target) state =
      .ok SailRV32.Functions.RETIRE_SUCCESS
        { state with regs := state.regs.insert .nextPC target } := by
  obtain ⟨bit0, bit1⟩ := aligned_access aligned
  obtain ⟨enabled, query⟩ := compressed_query read
  simp [SailRV32.Functions.jump_to, SailRV32.SailME.run, SailRV32.Functions.ext_control_check_pc,
    bit0, PreSail.assert, freeM_pure_bind]
  simp only [early_return_lift_bind]
  change run (SailRV32.Functions.currentlyEnabled .Ext_Zca >>= _) state = _
  rw [run_bind_of_ok _ _ _ _ _ query]
  simp only [bit1, SailRV32.Functions.bit_to_bool]
  rfl

/-- Machine mode with MLPE clear disables the native landing-pad update. This
    reads actual CSR state rather than replacing the instruction's extra effect. -/
theorem landing_pad_disabled (rs1 : SailRV32.regidx) {state : State} {security : BitVec 64}
    (privilege : run (SailRV32.readReg .cur_privilege) state = .ok .Machine state)
    (config : run (SailRV32.readReg .mseccfg) state = .ok security state)
    (disabled : SailRV32.Functions._get_Seccfg_MLPE security = 0) :
    run (SailRV32.Functions.update_elp_state rs1) state = .ok () state := by
  simp only [SailRV32.Functions.update_elp_state, SailRV32.Functions.currentlyEnabled,
    SailRV32.Functions.hartSupports, freeM_pure_bind, freeM_bind_assoc]
  rw [run_bind_of_ok _ _ _ _ _ privilege]
  simp only [SailRV32.Functions.get_xLPE, freeM_bind_assoc]
  rw [run_bind_of_ok _ _ _ _ _ config]
  simp [disabled, SailRV32.Functions.bool_bit_backwards, freeM_pure_bind]
  rfl

theorem clear_bit_zero (value : BitVec 32) :
    _root_.Sail.BitVec.update value 0 0#1 = value &&& 0xfffffffe := by
  simp [_root_.Sail.BitVec.update, _root_.Sail.BitVec.updateSubrange', BitVec.and_comm]

end Airbender.Reference.RiscV.Sail
