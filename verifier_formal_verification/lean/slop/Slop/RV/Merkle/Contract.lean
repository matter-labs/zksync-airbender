import Human.SpecMerkle
import Human.Delegations

/-! `merkle_step`'s contract (`merklePre` → `merklePost`): what `merkle_check`'s proof uses of it, without its proof
(`Step.lean`, `StepMop.lean`), so the two build in parallel. -/

namespace RV
open Spec

/-- The parent of the node at `a0` (`st.state`) and the sibling at `a2` (`a1 ≠ 0`: the node is the right child). -/
def merklePost (s s' : State) : Prop :=
  readWords s'.mem (s.getReg 10#5) 8 =
    if s.getReg 11#5 ≠ 0 then hash2 (readWords s.mem (s.getReg 12#5) 8) (readWords s.mem (s.getReg 10#5) 8)
    else hash2 (readWords s.mem (s.getReg 10#5) 8) (readWords s.mem (s.getReg 12#5) 8)

/-- The evaluator (`len` bytes, `al`-aligned) in RAM above `sp`, the sibling (8 words) in RAM above `sp`, outside
it. -/
def merklePre (al len : Nat) (s : State) : Prop :=
  (s.getReg 10#5).toNat % al = 0 ∧ (s.getReg 2#5).toNat ≤ (s.getReg 10#5).toNat ∧
  (s.getReg 10#5).toNat + len ≤ RAM_END ∧ (s.getReg 12#5).toNat % 4 = 0 ∧
  (s.getReg 2#5).toNat ≤ (s.getReg 12#5).toNat ∧ (s.getReg 12#5).toNat + 32 ≤ RAM_END ∧
  ((s.getReg 12#5).toNat + 32 ≤ (s.getReg 10#5).toNat ∨ (s.getReg 10#5).toNat + len ≤ (s.getReg 12#5).toNat)

end RV
