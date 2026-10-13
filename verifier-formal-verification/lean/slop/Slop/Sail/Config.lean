/-
# Sanity checks of the Airbender machine (each evaluated by the Lean kernel on the Sail model).
-/
import Slop.Sail.Airbender

open SailRV32

namespace Human

/-- Sail's initialisation (including its config validation) succeeds. -/
theorem init_ok : (match initResult with | .ok _ _ => true | .error _ _ => false) = true := by decide +kernel

/-- Machine mode after reset. -/
theorem stInit_machine : (stInit.regs .cur_privilege == Privilege.Machine) = true := by decide +kernel

/-- The reset state with one instruction `w` at address 0 (= the PC) and `a0 = 0x200004`. -/
noncomputable def test (w : BitVec 32) : FState :=
  { stInit.set .x10 0x200004 with mem := fun a => if a < 4 then w.extractLsb' (8 * a) 8 else 0 }

/-- what happens to the PC and the retired-instruction counter -/
noncomputable def outcome (w : BitVec 32) : Option (BitVec 32 × BitVec 64) :=
  (step (test w)).map fun s => (s.regs .PC, s.regs .minstret - stInit.regs .minstret)

theorem add_runs   : outcome 0x00b50533 = some (4, 1) := by decide +kernel  -- add a0, a0, a1
theorem mul_runs   : outcome 0x02b50533 = some (4, 1) := by decide +kernel  -- mul a0, a0, a1
theorem lw_runs    : outcome 0x00052583 = some (4, 1) := by decide +kernel  -- lw a1, 0(a0)
theorem csr_skips  : outcome 0x7c051073 = some (4, 1) := by decide +kernel  -- csrrw x0, 0x7c0, a0
theorem fence_stops : outcome 0x0ff0000f = none := by decide +kernel        -- fence
theorem ecall_stops : outcome 0x00000073 = none := by decide +kernel        -- ecall
theorem unimp_stops : outcome 0xc0001073 = none := by decide +kernel        -- csrrw x0, cycle, x0 (Airbender abort)
theorem rvc_stops   : outcome 0x00000505 = none := by decide +kernel        -- c.addi a0, 1 (no C extension)
theorem flw_stops   : outcome 0x00052007 = none := by decide +kernel        -- flw (no F extension)
theorem lw_misaligned_traps : outcome 0x00152583 = some (0, 0) := by decide +kernel  -- lw a1, 1(a0): trap to mtvec = 0
theorem sw_rom_traps : outcome 0x00b02023 = some (0, 0) := by decide +kernel  -- sw a1, 0(x0): ROM is read-only

end Human
