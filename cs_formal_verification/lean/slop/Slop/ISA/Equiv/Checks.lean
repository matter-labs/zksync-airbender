import Human.ISA.Sail.Checks

/-! `Airbender.MachineChecks`: each conjunct evaluated by the Lean kernel on the Sail model, in groups (one
theorem each, so they are checked independently). -/

open Sail SailRV32 SailRV32.Functions Human

namespace Airbender

/-- Sail's reset (with its config validation) succeeds, in machine mode. -/
theorem checks1 :
    (match sailResetRun with | .ok _ _ => true | .error _ _ => false) = true ∧
    (resetState.regs .cur_privilege == Privilege.Machine) = true
    := by decide +kernel

/-- What Airbender overrides, Sail rejects: `csrrw a0, 0x7c0, x0` (input), `csrrw x0, 0x7c7, x0` (a delegation). -/
theorem checks2 :
    sailRejects (.CSRReg (0x7c0, .Regidx 0, .Regidx 10, .CSRRW)) = true ∧
    sailRejects (.CSRReg (0x7c7, .Regidx 0, .Regidx 0, .CSRRW)) = true
    := by decide +kernel

/-- Plain RV32IM, and Sail's hint encodings run as plain instructions. -/
theorem checks3 :
    nextPC 0x00b50533 = some 4 ∧         -- add a0, a0, a1
    nextPC 0x02b50533 = some 4 ∧         -- mul a0, a0, a1
    nextPC 0x02b53533 = some 4 ∧         -- mulhu a0, a0, a1
    nextPC 0x00052583 = some 4 ∧         -- lw a1, 0(a0)
    nextPC 0x00200033 = some 4 ∧         -- add x0, x0, x2 (Zihintntl NTL hint in Sail)
    nextPC 0x00056013 = some 4         -- ori x0, a0, 0 (Zicbop prefetch in Sail)
    := by decide +kernel

/-- Airbender: a load into x0 only advances the PC. -/
theorem checks4 :
    nextPC 0x00152003 = some 4         -- lw x0, 1(a0): misaligned, but rd = x0
    := by decide +kernel

/-- Zbb/Zbkb rev8, Airbender's mop.r.N (xor-rotate), mop.rr.N and mop.r.N into x0 (no-ops). -/
theorem checks5 :
    nextPC 0x6985d513 = some 4 ∧         -- rev8 a0, a1
    nextPC 0xc1c5c573 = some 4 ∧         -- mop.r.16 a0, a1
    nextPC 0x82b54073 = some 4 ∧         -- mop.rr.0 x0, a0, a1
    nextPC 0xcdc5c073 = some 4         -- mop.r.28 x0, a1 (Zicfiss's encoding; Zicfiss is off)
    := by decide +kernel

/-- No step: not in Airbender, traps, the abort. -/
theorem checks6 :
    nextPC 0x40b52533 = none ∧           -- slt with funct7 = 0100000 (Airbender decodes funct7 exactly)
    nextPC 0x85d5c573 = none ∧           -- mop.r.5 a0, a1 (only 16, 12, 8, 7 into a register)
    nextPC 0x00051067 = none ∧           -- jalr x0, 0(a0) with funct3 = 1
    nextPC 0x02b51533 = none ∧           -- mulh
    nextPC 0x02b54533 = none ∧           -- div
    nextPC 0x0ff0000f = none ∧           -- fence
    nextPC 0x00000073 = none ∧           -- ecall
    nextPC 0x00052007 = none ∧           -- flw (no F extension)
    nextPC 0x00000505 = none ∧           -- c.addi a0, 1 (no C extension)
    nextPC 0x00152583 = none ∧           -- lw a1, 1(a0): misaligned
    nextPC 0x00b02023 = none ∧           -- sw a1, 0(x0): ROM
    nextPC 0xc0001073 = none           -- csrrw x0, cycle, x0 (Airbender's abort)
    := by decide +kernel

/-- CSR 0x7c0: input read, write (no effect), and the rejected forms. -/
theorem checks7 :
    readNext 0x7c001573 [0x1234] = some (4, 0x1234, []) ∧  -- csrrw a0, 0x7c0, x0
    readNext 0x7c001573 [] = none ∧                         -- … with the input used up
    readNext 0x7c002573 [0x1234] = none ∧                   -- csrrs a0, 0x7c0, x0
    readNext 0x7c007573 [0x1234] = none ∧                   -- csrrci a0, 0x7c0, 0
    nextPC 0x7c051073 = some 4 ∧         -- csrrw x0, 0x7c0, a0: no effect
    nextPC 0x7c02d073 = none ∧           -- csrrwi x0, 0x7c0, 5
    nextPC 0x7c051573 = none ∧           -- csrrw a0, 0x7c0, a0
    nextPC 0x7c001073 = none           -- csrrw x0, 0x7c0, x0
    := by decide +kernel

/-- Delegation calls: run by `RV.Delegation`, rejected on bad arguments. -/
theorem checks8 :
    nextPC 0x7c701073 = none ∧           -- Blake2s round with x12 = 0
    nextPC 0x7c801073 = none ∧           -- Blake2s G with x10 not 64-aligned
    (step ⟨(testState 0x7c701073).set .x12 0x90000#32, []⟩).isNone = true  -- x10 not 128-aligned, x11 in ROM
    := by decide +kernel

theorem machine_checks : MachineChecks := by
  exact ⟨checks1.1, checks1.2, checks2.1, checks2.2, checks3.1, checks3.2.1, checks3.2.2.1, checks3.2.2.2.1,
    checks3.2.2.2.2.1, checks3.2.2.2.2.2, checks4, checks5.1, checks5.2.1, checks5.2.2.1, checks5.2.2.2, checks6.1,
    checks6.2.1, checks6.2.2.1, checks6.2.2.2.1, checks6.2.2.2.2.1, checks6.2.2.2.2.2.1, checks6.2.2.2.2.2.2.1,
    checks6.2.2.2.2.2.2.2.1, checks6.2.2.2.2.2.2.2.2.1, checks6.2.2.2.2.2.2.2.2.2.1, checks6.2.2.2.2.2.2.2.2.2.2.1,
    checks6.2.2.2.2.2.2.2.2.2.2.2, checks7.1, checks7.2.1, checks7.2.2.1, checks7.2.2.2.1, checks7.2.2.2.2.1,
    checks7.2.2.2.2.2.1, checks7.2.2.2.2.2.2.1, checks7.2.2.2.2.2.2.2, checks8.1, checks8.2.1, checks8.2.2⟩

end Airbender
