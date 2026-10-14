/-
# What "the code at `entry` implements a function" means (RISC-V C calling convention, RV32).
-/
import Slop.Sail.Airbender
import Image

open SailRV32

namespace Human

/-- The flat image `build/app.bin` is in memory at address 0. -/
def ImageLoaded (s : SailState) : Prop := ∀ i (h : i < Image.bytes.size), s.mem i = Image.bytes[i]

/-- Registers a callee must preserve: sp, s0..s11. -/
def CalleeSaved : Register → Bool
  | .x2 | .x8 | .x9 | .x18 | .x19 | .x20 | .x21 | .x22 | .x23 | .x24 | .x25 | .x26 | .x27 => true
  | _ => false

/-- Called at `entry` with a 16-aligned stack pointer `sp` in RAM with at least `frame` bytes free below it,
and with `pre` holding, the code runs finitely many normally-retiring instructions and returns to `ra`,
with `post` holding, callee-saved registers restored, and memory changed only in `[sp - frame, sp)`. -/
def Implements (entry frame : Nat) (pre : SailState → Prop) (post : SailState → SailState → Prop) : Prop :=
  ∀ s, Configured s → ImageLoaded s → (s.regs .PC).toNat = entry → pre s →
    let sp := (s.regs .x2).toNat
    sp % 16 = 0 → RAM_START + frame ≤ sp → sp ≤ RAM_END →
    ∃ n s', Runs n s s' ∧ Configured s' ∧ s'.regs .PC = s.regs .x1 ∧ post s s' ∧
      (∀ r, CalleeSaved r = true → s'.regs r = s.regs r) ∧
      (∀ a, (a < sp - frame ∨ sp ≤ a) → s'.mem a = s.mem a)

/-- A function `u32 → u32`: argument and result in a0. -/
def Implements₁ (entry frame : Nat) (f : BitVec 32 → BitVec 32) : Prop :=
  Implements entry frame (fun _ => True) (fun s s' => s'.regs .x10 = f (s.regs .x10))

end Human
