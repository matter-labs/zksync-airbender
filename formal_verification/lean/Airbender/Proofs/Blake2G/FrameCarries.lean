import Airbender.Proofs.Blake2G.Frame

namespace Airbender.Blake2G.Proofs
open Arithmetic
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

/-- All embeddings share this carry argument. Ternary native addition carries
    give two Boolean bits; two-input additions supply their own Boolean carry. -/
theorem Frame.flags_of_bounds {p : Nat} [Fact p.Prime] (frame : Frame p)
    (addition : ∀ slot : Fin 4, frame.addCarries[slot].val < 3)
    (twoInput : ∀ slot : Fin 4, frame.cCarries[slot] = 0 ∨ frame.cCarries[slot] = 1)
    (k : Fin 12) :
    frame.base Variables.booleanColumns[1 + k.val] = 0 ∨
      frame.base Variables.booleanColumns[1 + k.val] = 1 := by
  have a0 := carry_flags (addition 0)
  have a1 := carry_flags (addition 1)
  have a2 := carry_flags (addition 2)
  have a3 := carry_flags (addition 3)
  have c0 := twoInput 0
  have c1 := twoInput 1
  have c2 := twoInput 2
  have c3 := twoInput 3
  fin_cases k
  all_goals simp only [Frame.base, Variables.booleanColumns,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, Nat.reduceAdd]
  all_goals first
    | exact a0.1
    | exact a0.2
    | exact a1.1
    | exact a1.2
    | exact a2.1
    | exact a2.2
    | exact a3.1
    | exact a3.2
    | exact c0
    | exact c1
    | exact c2
    | exact c3

end Airbender.Blake2G.Proofs
