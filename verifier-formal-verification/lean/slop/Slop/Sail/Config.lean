/-
# Sanity checks of the Airbender machine (each evaluated by the Lean kernel on the Sail model).
-/
import Slop.Sail.Airbender

open SailRV32

namespace Human

/-- Sail's initialisation (including its config validation) succeeds. -/
theorem init_ok : (match initResult with | .ok _ _ => true | .error _ _ => false) = true := by decide +kernel

/-- Machine mode after reset. -/
theorem stInit_machine : (resetState.regs .cur_privilege == Privilege.Machine) = true := by decide +kernel

/-- The reset state with one instruction `w` at address 0 (= the PC) and `a0 = 0x400004`. -/
noncomputable def test (w : BitVec 32) : SailState :=
  { resetState.set .x10 0x400004 with mem := fun a => if a < 4 then w.extractLsb' (8 * a) 8 else 0 }

/-- what happens to the PC and the retired-instruction counter -/
noncomputable def outcome (w : BitVec 32) : Option (BitVec 32 × BitVec 64) :=
  (step (test w)).map fun s => (s.regs .PC, s.regs .minstret - resetState.regs .minstret)

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

/-! The Airbender machine (`HumanSail/Airbender.lean`): where the PC goes, one check per change from Sail. -/
noncomputable def next (w : BitVec 32) : Option (BitVec 32) := (Airbender.step (test w)).map (·.regs .PC)

theorem add_next     : next 0x00b50533 = some 4 := by decide +kernel         -- add a0, a0, a1
theorem ntl_next     : next 0x00200033 = some 4 := by decide +kernel         -- add x0, x0, x2 (Sail+Zihintntl: NTL hint)
theorem ori_x0_next  : next 0x00056013 = some 4 := by decide +kernel         -- ori x0, a0, 0 (Sail+Zicbop: prefetch)
theorem mulhu_next   : next 0x02b53533 = some 4 := by decide +kernel         -- mulhu a0, a0, a1
theorem mulh_stops   : next 0x02b51533 = none := by decide +kernel           -- mulh: not in Airbender
theorem div_stops    : next 0x02b54533 = none := by decide +kernel           -- div: not in Airbender
theorem slt_f7_next  : next 0x40b52533 = some 4 := by decide +kernel         -- slt with funct7 = 0100000
theorem jalr_f3_next : next 0x00051067 = some 0x400004 := by decide +kernel  -- jalr x0, 0(a0) with funct3 = 1
theorem lw_x0_next   : next 0x00152003 = some 4 := by decide +kernel         -- lw x0, 1(a0): misaligned, but rd = x0
theorem lw_mis_stops : next 0x00152583 = none := by decide +kernel           -- lw a1, 1(a0): misaligned
theorem sw_rom_stops : next 0x00b02023 = none := by decide +kernel           -- sw a1, 0(x0): ROM
theorem rvc_stops'   : next 0x00000505 = none := by decide +kernel           -- c.addi a0, 1
theorem csr_stops    : next 0x7c051073 = none := by decide +kernel           -- csrrw x0, 0x7c0, a0 (not modelled yet)

end Human
