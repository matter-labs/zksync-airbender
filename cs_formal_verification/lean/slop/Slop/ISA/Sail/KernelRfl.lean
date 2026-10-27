import Lean
import Slop.Sail.Configured

/-! `kernel_rfl`: close `a = b` with `Eq.refl a`, checked ONLY by the Lean kernel (the elaborator's
definitional-equality check is skipped; it is far slower on the generated Sail model). The tactic is the circuit
proofs' (`Slop/Sail/Configured.lean`); this file adds the helper the ISA proofs' own tactics use. -/

open Lean Meta Elab Tactic

/-- `proof : ty` as an auxiliary theorem, kernel-checked now (not in the background), so a failure is an
exception the caller can catch. -/
def mkAuxTheoremNow (ty proof : Expr) : MetaM Expr :=
  withOptions (fun o => Elab.async.set (maxRecDepth.set o 1000000) false) (mkAuxTheorem ty proof)

example (n : Nat) : (fun x => x + 0) n = n := by kernel_rfl
