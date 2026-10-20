import HumanSail.Airbender

/-! # The Airbender machine on single instructions (part of the final theorems)

The final theorems (`Theorems.lean`) hold for every `Configured` start state; these checks pin down the machine
they are about. Sail's reset succeeds in machine mode; where Airbender gives an instruction a meaning of its own
(`execute`: the input CSR, the delegation calls) Sail's own semantics rejects it, so each change from Sail only
gives meaning to a trapping instruction; and one step of the machine on representative words: from the reset state
with the word at address 0 and `a0 = 0x400004` (in RAM), the next PC, or `none` (no step). -/

open Sail SailRV32 SailRV32.Functions Human

namespace Airbender

/-- The reset state with one instruction `w` at address 0 (= the PC) and `a0 = 0x400004`. -/
noncomputable def testState (w : BitVec 32) : SailState :=
  { resetState.set .x10 0x400004 with mem := fun a => if a < 4 then w.extractLsb' (8 * a) 8 else 0 }

/-- The PC after one step of the machine on `w` (input `[0x1234]`). -/
noncomputable def nextPC (w : BitVec 32) : Option (BitVec 32) :=
  (step ⟨testState w, [0x1234]⟩).map (·.sail.regs .PC)

/-- An input read: the PC, `a0` and the input left. -/
noncomputable def readNext (w : BitVec 32) (input : List (BitVec 32)) :
    Option (BitVec 32 × BitVec 32 × List (BitVec 32)) :=
  (step ⟨testState w, input⟩).map fun m => (m.sail.regs .PC, m.sail.regs .x10, m.input)

/-- Sail's own `execute` of `i` from the reset state is an illegal instruction. -/
noncomputable def sailRejects (i : instruction) : Bool :=
  match runSail (SailRV32.Functions.execute i) resetState with | .ok (.Illegal_Instruction ()) _ => true | _ => false

def MachineChecks : Prop :=
  -- Sail's reset (with its config validation) succeeds, in machine mode
  (match sailResetRun with | .ok _ _ => true | .error _ _ => false) = true ∧
  (resetState.regs .cur_privilege == Privilege.Machine) = true ∧
  -- what Airbender overrides, Sail rejects: `csrrw a0, 0x7c0, x0` (input), `csrrw x0, 0x7c7, x0` (a delegation)
  sailRejects (.CSRReg (0x7c0, .Regidx 0, .Regidx 10, .CSRRW)) = true ∧
  sailRejects (.CSRReg (0x7c7, .Regidx 0, .Regidx 0, .CSRRW)) = true ∧
  -- plain RV32IM, and Sail's hint encodings run as plain instructions
  nextPC 0x00b50533 = some 4 ∧         -- add a0, a0, a1
  nextPC 0x02b50533 = some 4 ∧         -- mul a0, a0, a1
  nextPC 0x02b53533 = some 4 ∧         -- mulhu a0, a0, a1
  nextPC 0x00052583 = some 4 ∧         -- lw a1, 0(a0)
  nextPC 0x00200033 = some 4 ∧         -- add x0, x0, x2 (Zihintntl NTL hint in Sail)
  nextPC 0x00056013 = some 4 ∧         -- ori x0, a0, 0 (Zicbop prefetch in Sail)
  -- Airbender's extra encodings
  nextPC 0x40b52533 = some 4 ∧         -- slt with funct7 = 0100000
  nextPC 0x00051067 = some 0x400004 ∧  -- jalr x0, 0(a0) with funct3 = 1
  nextPC 0x00152003 = some 4 ∧         -- lw x0, 1(a0): misaligned, but rd = x0
  -- no step: not in Airbender, traps, the abort
  nextPC 0x02b51533 = none ∧           -- mulh
  nextPC 0x02b54533 = none ∧           -- div
  nextPC 0x0ff0000f = none ∧           -- fence
  nextPC 0x00000073 = none ∧           -- ecall
  nextPC 0x00052007 = none ∧           -- flw (no F extension)
  nextPC 0x00000505 = none ∧           -- c.addi a0, 1 (no C extension)
  nextPC 0x00152583 = none ∧           -- lw a1, 1(a0): misaligned
  nextPC 0x00b02023 = none ∧           -- sw a1, 0(x0): ROM
  nextPC 0xc0001073 = none ∧           -- csrrw x0, cycle, x0 (Airbender's abort)
  -- CSR 0x7c0: input read, write (no effect), and the rejected forms
  readNext 0x7c001573 [0x1234] = some (4, 0x1234, []) ∧  -- csrrw a0, 0x7c0, x0
  readNext 0x7c001573 [] = none ∧                         -- … with the input used up
  readNext 0x7c002573 [0x1234] = none ∧                   -- csrrs a0, 0x7c0, x0
  readNext 0x7c007573 [0x1234] = none ∧                   -- csrrci a0, 0x7c0, 0
  nextPC 0x7c051073 = some 4 ∧         -- csrrw x0, 0x7c0, a0: no effect
  nextPC 0x7c02d073 = none ∧           -- csrrwi x0, 0x7c0, 5
  nextPC 0x7c051573 = none ∧           -- csrrw a0, 0x7c0, a0
  nextPC 0x7c001073 = none ∧           -- csrrw x0, 0x7c0, x0
  -- delegation calls: run by `RV.Delegation`, rejected on bad arguments
  nextPC 0x7c701073 = none ∧           -- Blake2s round with x12 = 0
  nextPC 0x7c801073 = none ∧           -- Blake2s G with x10 not 64-aligned
  (step ⟨(testState 0x7c701073).set .x12 0x90000#32, []⟩).isNone = true  -- x10 not 128-aligned, x11 in ROM

end Airbender
