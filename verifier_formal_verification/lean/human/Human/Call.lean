import Human.RV32

/-! # What "this code implements a function" means (RISC-V C calling convention) -/

namespace RV

-- Register names of the calling convention.
namespace ABI
abbrev ra : Reg := 1   -- return address
abbrev sp : Reg := 2   -- stack pointer
abbrev a0 : Reg := 10  -- first argument / result
abbrev a1 : Reg := 11  -- second argument / result
end ABI
open ABI

/-- The instruction words `code` are in memory starting at address `addr`. -/
def CodeAt (s : State) (addr : Word) (code : List Word) : Prop :=
  ∀ i (h : i < code.length), read s.mem (addr + BitVec.ofNat 32 (4 * i)) 4 = code[i]

/-- sp, s0..s11 (x2, x8, x9, x18..x27): a function must give them back unchanged. -/
def calleeSaved (i : Reg) : Prop := i = sp ∨ i = 8 ∨ i = 9 ∨ (18 ≤ i.toNat ∧ i.toNat ≤ 27)

/-- A call into `code`: the code is at the PC (aligned, in ROM), the return address `ra` is aligned,
and the stack pointer `sp` is 16-aligned, in RAM, with `frameBytes` free bytes below it. -/
def Call (s : State) (code : List Word) (frameBytes : Nat) : Prop :=
  CodeAt s s.pc code ∧ s.pc.toNat % 4 = 0 ∧ s.pc.toNat + 4 * code.length ≤ ROM_END ∧
  (s.getReg ra).toNat % 4 = 0 ∧
  (s.getReg sp).toNat % 16 = 0 ∧ ROM_END + frameBytes ≤ (s.getReg sp).toNat ∧ (s.getReg sp).toNat ≤ RAM_END

/-- After some steps we are back at `ra` with `post before after` holding, callee-saved registers restored, and
memory changed only in the stack frame `[sp - frameBytes, sp)`. -/
def Returns (before : State) (frameBytes : Nat) (post : State → State → Prop) : Prop :=
  ∃ numSteps after, run numSteps before = some after ∧ after.pc = before.getReg ra ∧ post before after ∧
    (∀ i, calleeSaved i → after.getReg i = before.getReg i) ∧
    (∀ addr : Word, addr.toNat + frameBytes < (before.getReg sp).toNat ∨ (before.getReg sp).toNat ≤ addr.toNat →
      after.mem addr = before.mem addr)

/-- `code` implements `post`, wherever it is placed. -/
def Implements (code : List Word) (frameBytes : Nat) (post : State → State → Prop) : Prop :=
  ∀ start, Call start code frameBytes → Returns start frameBytes post

/-- `code` placed at `entry` implements `post`, given the code of the functions it calls (`callees`: their
(address, code) pairs). `frameBytes` includes the callees' frames. -/
def ImplementsAt (entry : Word) (code : List Word) (callees : List (Word × List Word)) (frameBytes : Nat)
    (post : State → State → Prop) : Prop :=
  ∀ start, start.pc = entry → (∀ callee ∈ callees, CodeAt start callee.1 callee.2) →
    Call start code frameBytes → Returns start frameBytes post

/-- The code computes `f : u32 → u32`: argument and result in `a0`. -/
def mapsA0 (f : Word → Word) : State → State → Prop :=
  fun before after => after.getReg a0 = f (before.getReg a0)

end RV
