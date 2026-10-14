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
and the stack pointer `sp` is 16-aligned, in RAM, with `frame` free bytes below it. -/
def Call (s : State) (code : List Word) (frame : Nat) : Prop :=
  CodeAt s s.pc code ∧ s.pc.toNat % 4 = 0 ∧ s.pc.toNat + 4 * code.length ≤ ROM_END ∧
  (s.getReg ra).toNat % 4 = 0 ∧
  (s.getReg sp).toNat % 16 = 0 ∧ ROM_END + frame ≤ (s.getReg sp).toNat ∧ (s.getReg sp).toNat ≤ RAM_END

/-- After some steps we are back at `ra` with `post` holding, callee-saved registers restored, and memory
changed only in the stack frame `[sp - frame, sp)`. -/
def Returns (s : State) (frame : Nat) (post : State → State → Prop) : Prop :=
  ∃ numSteps s', run numSteps s = some s' ∧ s'.pc = s.getReg ra ∧ post s s' ∧
    (∀ i, calleeSaved i → s'.getReg i = s.getReg i) ∧
    (∀ addr : Word, addr.toNat + frame < (s.getReg sp).toNat ∨ (s.getReg sp).toNat ≤ addr.toNat →
      s'.mem addr = s.mem addr)

/-- `code` implements `post`, wherever it is placed. -/
def Implements (code : List Word) (frame : Nat) (post : State → State → Prop) : Prop :=
  ∀ s, Call s code frame → Returns s frame post

/-- `code` placed at `entry` implements `post`, given the code of the functions it calls at their addresses.
(`frame` includes the callees' frames.) -/
def ImplementsAt (entry : Word) (code : List Word) (callees : List (Word × List Word)) (frame : Nat)
    (post : State → State → Prop) : Prop :=
  ∀ s, s.pc = entry → (∀ c ∈ callees, CodeAt s c.1 c.2) → Call s code frame → Returns s frame post

/-- The code computes `f : u32 → u32`: argument and result in `a0`. -/
def mapsA0 (f : Word → Word) : State → State → Prop := fun s s' => s'.getReg a0 = f (s.getReg a0)

end RV
