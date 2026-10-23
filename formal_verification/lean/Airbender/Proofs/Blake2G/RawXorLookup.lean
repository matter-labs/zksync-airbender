import Airbender.Proofs.Blake2G.Tables

namespace Airbender.Blake2G.Proofs
set_option warningAsError true
set_option Elab.async false

/-- Apply typed XOR soundness once to a raw native lookup, retaining all columns. -/
theorem xor_lookup_raw {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 512)
    {control : Fin 512 → Vector Nat 7} {query : Lookup (ZMod p)}
    {env : Environment (ZMod p)} (kind : Fin 5)
    (h : query.Contains env) (table : query.table = (setupTable control).toRaw)
    (selected : query.entry.toArray[8]!.eval env =
      ((#v[4, 17, 18, 19, 20][kind] : Nat) : ZMod p)) :
    (query.entry.toArray[0]!.eval env).val < 2 ^ (#v[8, 3, 4, 7, 9][kind]) ∧
    (query.entry.toArray[1]!.eval env).val < 2 ^ (#v[8, 3, 4, 7, 9][kind]) ∧
    (query.entry.toArray[2]!.eval env).val < 2 ^ (#v[8, 3, 4, 7, 9][kind]) ∧
    (query.entry.toArray[2]!.eval env).val =
      (query.entry.toArray[0]!.eval env).val ^^^ (query.entry.toArray[1]!.eval env).val := by
  rcases query with ⟨raw, entry⟩
  cases table
  have get (j : Nat) (hj : j < 9) : entry.toArray[j]! = entry[j] := by
    rw [getElem!_pos entry.toArray j (by rw [entry.size_toArray]; exact hj)]
    rfl
  simpa only [get 0 (by decide), get 1 (by decide), get 2 (by decide)] using
    xor_lookup hp kind h (by simpa only [get 8 (by decide)] using selected)

end Airbender.Blake2G.Proofs
