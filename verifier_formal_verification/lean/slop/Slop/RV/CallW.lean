import Slop.RV.Tactic

/-! Calls that may also write an out-parameter: `len` bytes at the address passed in `a0` (Rust `&mut`), outside
the callee's stack frame. -/

namespace RV
open ABI

/-- `Returns`, where memory may also change in `[dst, dst + len)`. -/
def ReturnsW (before : State) (frameBytes : Nat) (dst : Word) (len : Nat) (post : State → State → Prop) : Prop :=
  ∃ numSteps after, run numSteps before = some after ∧ after.pc = before.getReg ra ∧ post before after ∧
    (∀ i, calleeSaved i → after.getReg i = before.getReg i) ∧
    (∀ addr : Word, addr.toNat + frameBytes < (before.getReg sp).toNat ∨ (before.getReg sp).toNat ≤ addr.toNat →
      addr.toNat < dst.toNat ∨ dst.toNat + len ≤ addr.toNat → after.mem addr = before.mem addr)

/-- `ImplementsAtPre` for a function writing `len` bytes at `a0`. -/
def ImplementsAtW (entry : Word) (code : List Word) (callees : List (Word × List Word)) (frame : Nat)
    (pre : State → Prop) (len : Nat) (post : State → State → Prop) : Prop :=
  ∀ s, s.pc = entry → (∀ c ∈ callees, CodeAt s c.1 c.2) → Call s code frame → pre s →
    ReturnsW s frame (s.getReg a0) len post

theorem run_callAtW {entry : Word} {code : List Word} {callees : List (Word × List Word)} {frame len : Nat}
    {pre : State → Prop} {post : State → State → Prop} (hI : ImplementsAtW entry code callees frame pre len post)
    (S : State) (P : State → Prop) (hpc : S.pc = entry) (hcal : ∀ c ∈ callees, CodeAt S c.1 c.2)
    (hc : Call S code frame) (hpre : pre S)
    (h : ∀ S1, S1.pc = S.getReg 1 → post S S1 → (∀ i, calleeSaved i → S1.getReg i = S.getReg i) →
      (∀ a : Word, a.toNat + frame < (S.getReg 2).toNat ∨ (S.getReg 2).toNat ≤ a.toNat →
        a.toNat < (S.getReg 10).toNat ∨ (S.getReg 10).toNat + len ≤ a.toNat → S1.mem a = S.mem a) →
      ∃ m s', run m S1 = some s' ∧ P s') : ∃ m s', run m S = some s' ∧ P s' := by
  obtain ⟨n, S1, h1, h2, h3, h4, h5⟩ := hI S hpc hcal hc hpre
  exact run_of_run S S1 n P h1 (h S1 h2 h3 h4 h5)

/-- `rv_frame` for `ReturnsW`. -/
syntax "rv_frameW" (" with " term,*)? : tactic
macro_rules
  | `(tactic| rv_frameW $[with $xs,*]?) => do
    let xs' : Array Lean.Term := xs.map (·.getElems) |>.getD #[]
    let xs : Array (Lean.TSyntax `Lean.Parser.Tactic.simpLemma) ← xs'.mapM
      fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
    `(tactic| (
      intro a ha hb
      simp (disch := rv_disch with $xs',*) only [set_mem, jump_mem, next_mem, store_mem, write_outside, $xs,*]))

end RV
