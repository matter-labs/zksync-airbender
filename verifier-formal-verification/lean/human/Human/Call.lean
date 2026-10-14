import Human.RV32

/-! # What "this code implements a function" means (RISC-V C calling convention) -/

namespace RV

/-- The instruction words `code` are in memory starting at address `a`. -/
def CodeAt (s : State) (a : Word) (code : List Word) : Prop :=
  ∀ i (h : i < code.length), read s.mem (a + BitVec.ofNat 32 (4 * i)) 4 = code[i]

/-- sp, s0..s11: a function must give them back unchanged. -/
def calleeSaved (i : Reg) : Prop := i = 2 ∨ i = 8 ∨ i = 9 ∨ (18 ≤ i.toNat ∧ i.toNat ≤ 27)

/-- A call into `code`: the code is at the PC (aligned, in ROM), the return address `ra = x1` is aligned,
and the stack pointer `sp = x2` is 16-aligned, in RAM, with `frame` free bytes below it. -/
def Call (s : State) (code : List Word) (frame : Nat) : Prop :=
  CodeAt s s.pc code ∧ s.pc.toNat % 4 = 0 ∧ s.pc.toNat + 4 * code.length ≤ ROM_END ∧
  (s.getReg 1).toNat % 4 = 0 ∧ (s.getReg 2).toNat % 16 = 0 ∧ ROM_END + frame ≤ (s.getReg 2).toNat ∧ (s.getReg 2).toNat ≤ RAM_END

/-- After some steps we are back at `ra` with `post` holding, callee-saved registers restored, and memory
changed only in the stack frame `[sp - frame, sp)`. -/
def Returns (s : State) (frame : Nat) (post : State → State → Prop) : Prop :=
  ∃ n s', run n s = some s' ∧ s'.pc = s.getReg 1 ∧ post s s' ∧
    (∀ i, calleeSaved i → s'.getReg i = s.getReg i) ∧
    (∀ a : Word, a.toNat + frame < (s.getReg 2).toNat ∨ (s.getReg 2).toNat ≤ a.toNat → s'.mem a = s.mem a)

/-- `code` implements `post`, wherever it is placed. -/
def Implements (code : List Word) (frame : Nat) (post : State → State → Prop) : Prop :=
  ∀ s, Call s code frame → Returns s frame post

/-- `code` placed at `entry` implements `post`, given the code of the functions it calls at their addresses.
(`frame` includes the callees' frames.) -/
def ImplementsAt (entry : Word) (code : List Word) (callees : List (Word × List Word)) (frame : Nat)
    (post : State → State → Prop) : Prop :=
  ∀ s, s.pc = entry → (∀ c ∈ callees, CodeAt s c.1 c.2) → Call s code frame → Returns s frame post

/-- A function `u32 → u32`: argument and result in a0 = x10. -/
def fn₁ (f : Word → Word) : State → State → Prop := fun s s' => s'.getReg 10 = f (s.getReg 10)

end RV
