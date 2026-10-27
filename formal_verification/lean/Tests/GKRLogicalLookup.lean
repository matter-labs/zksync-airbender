import Airbender.Proofs.GKRProtocol.LogicalLookup
import Airbender.Proofs.GKRProtocol.LogicalLookupSegments

namespace Tests.GKRLogicalLookup
open Airbender.Compiler
set_option warningAsError true

def table : Fin 2 → Nat
  | ⟨0, _⟩ => 7
  | ⟨1, _⟩ => 9

/-- Repeated requests must retain their natural multiplicity. -/
def repeated : LookupArgument table [7, 9, 7] := {
  rows := [0, 1]
  multiplicity := fun index => if index = 0 then 2 else 1
  balance := by decide +kernel }

example : ∃ row, 9 = table row := LookupArgument.member repeated (by decide)

/-- Per-row matching is obtained from the trace-wide argument, rather than
supplied as an independent source-membership fact. -/
noncomputable def suffix : LookupArgument table [9, 7] :=
  LookupArgument.segment (chunks := [[7], [9, 7]]) repeated (by simp)

example : ∃ row, 7 = table row := LookupArgument.member suffix (by decide)

/-- An absent tuple cannot be introduced by a choice of multiplicities or
duplicate setup indices. This is stronger than a sampled field-sum equation. -/
example : ¬ Nonempty (LookupArgument table [8]) := by
  rintro ⟨argument⟩
  obtain ⟨row, same⟩ := LookupArgument.member (query := 8) argument (by simp)
  fin_cases row <;> norm_num [table] at same

end Tests.GKRLogicalLookup
