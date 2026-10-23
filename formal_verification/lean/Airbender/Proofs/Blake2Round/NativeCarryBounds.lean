import Airbender.Proofs.Blake2Round.NativeXorTransfer

namespace Airbender.Blake2Round.Proofs
set_option warningAsError true

/-- Reuse a checked vector evaluation when reading the carry and tag columns. -/
theorem carry_values_bound {p : Nat} [Fact p.Prime]
    (hp : FieldCapacity.AtLeast p 512) (kind : Fin 2)
    {source : Vector (Expression (ZMod p)) 6} {values : Vector (ZMod p) 6}
    {env : Environment (ZMod p)} (member : (Lookup.mk setupTable.toRaw source).Contains env)
    (evaluated : source.map (Expression.eval env) = values)
    (selected : values[5] = ((carryTags[kind] : Nat) : ZMod p)) : values[2].val < 3 := by
  have tag := congrArg (fun row : Vector (ZMod p) 6 => row[5]) evaluated
  have value := congrArg (fun row : Vector (ZMod p) 6 => row[2]) evaluated
  simp only [Vector.getElem_map] at tag value
  have bound := carry_value_bound hp kind member (tag.trans selected)
  rw [value] at bound
  exact bound

end Airbender.Blake2Round.Proofs
