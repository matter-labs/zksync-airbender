import Airbender.Proofs.Blake2Round.NativeXorTransfer
import Airbender.Proofs.Blake2G.Tables
import Airbender.Proofs.Constraints

namespace Airbender.Blake2Round.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

/-- Ordinary native regions project to the same imported G XOR rows. Carry and
    packed regions have their separate checked projections. -/
theorem padded_membership {p : Nat} [Fact p.Prime] (hp : 512 ≤ p)
    {source : Vector (Expression (ZMod p)) 6} {target : Vector (Expression (ZMod p)) 9}
    {sourceEnv targetEnv : Environment (ZMod p)} (kind : Fin 3)
    (h : (Lookup.mk setupTable.toRaw source).Contains sourceEnv)
    (tag : source[5].eval sourceEnv = ((plainTags[kind] : Nat) : ZMod p))
    (columns : target.map (Expression.eval targetEnv) = plainPad (source.map (Expression.eval sourceEnv))) :
    (Lookup.mk (Blake2G.setupTable (fun _ => Vector.replicate 7 0)).toRaw target).Contains targetEnv :=
  plain_membership hp _ kind h tag columns

theorem xor_lookup {p : Nat} [Fact p.Prime] (hp : 512 ≤ p)
    {entry : Vector (Expression (ZMod p)) 6} {env : Environment (ZMod p)}
    (kind : Fin 3) (h : (Lookup.mk setupTable.toRaw entry).Contains env)
    (selected : entry[5].eval env = ((plainTags[kind] : Nat) : ZMod p)) :
    (entry[0].eval env).val < plainBase[kind] ∧
    (entry[1].eval env).val < plainBase[kind] ∧
    (entry[2].eval env).val < plainBase[kind] ∧
    (entry[2].eval env).val = (entry[0].eval env).val ^^^ (entry[1].eval env).val := by
  let padded : Vector (Expression (ZMod p)) 9 :=
    #v[entry[0], entry[1], entry[2], .const 0, .const 0, .const 0, .const 0, .const 0, entry[5]]
  have member := plain_membership hp (fun _ => Vector.replicate 7 0) kind h selected
    (target := padded) (targetEnv := env) (by ext j hj; interval_cases j <;> simp [padded, plainPad, Expression.eval])
  have tag : padded[8].eval env = ((gTags[plainGKind[kind]] : Nat) : ZMod p) := by
    fin_cases kind <;> simpa [padded, gTags, plainGKind, plainTags] using selected
  have result := Blake2G.Proofs.xor_lookup hp plainGKind[kind] member tag
  fin_cases kind <;> simpa [padded, plainBase, plainGKind] using result

/-- Raw queries retain all six physical columns, including their native tag. -/
theorem xor_lookup_raw {p : Nat} [Fact p.Prime] (hp : 512 ≤ p)
    {query : Lookup (ZMod p)} {env : Environment (ZMod p)} (kind : Fin 3)
    (h : query.Contains env) (table : query.table = setupTable.toRaw)
    (selected : (query.entry.toArray[5]!).eval env = ((plainTags[kind] : Nat) : ZMod p)) :
    (query.entry.toArray[0]!.eval env).val < plainBase[kind] ∧
    (query.entry.toArray[1]!.eval env).val < plainBase[kind] ∧
    (query.entry.toArray[2]!.eval env).val < plainBase[kind] ∧
    (query.entry.toArray[2]!.eval env).val =
      (query.entry.toArray[0]!.eval env).val ^^^ (query.entry.toArray[1]!.eval env).val := by
  rcases query with ⟨raw, entry⟩
  cases table
  have get (j : Nat) (hj : j < 6) : entry.toArray[j]! = entry[j] := by
    rw [getElem!_pos entry.toArray j (by rw [entry.size_toArray]; exact hj)]
    rfl
  simpa only [get 0 (by decide), get 1 (by decide), get 2 (by decide)] using
    xor_lookup hp kind h (by simpa only [get 5 (by decide)] using selected)

/-- Membership identifies the exact ordinary, carry-aware, or packed region. -/
theorem xor_lookup_any {p : Nat} [Fact p.Prime]
    {entry : Vector (Expression (ZMod p)) 6} {env : Environment (ZMod p)}
    (h : (Lookup.mk setupTable.toRaw entry).Contains env) :
    ∃ kind : Fin 6, ∃ n, n < nativeLengths[kind] ∧
      entry.map (Expression.eval env) =
        (referenceRegionRow kind n).map (fun value : Nat => (value : ZMod p)) :=
  any_region h

/-- All 192 generic native queries use the imported six-region setup. -/
theorem data_lookups {p : Nat} [Fact p.Prime] {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    ∀ query ∈ (FlatOperation.lookups (importedConstraints setupTable)).drop 2,
      query.table = setupTable.toRaw ∧ query.Contains (Verification.environment w) := by
  have tables : ∀ query ∈ (FlatOperation.lookups (importedConstraints (p := p) setupTable)).drop 2,
      query.table = setupTable.toRaw := by
    dsimp only [importedConstraints, FlatOperation.lookups, List.drop]
    simp only [List.forall_mem_cons, true_and]
    exact List.forall_mem_nil _
  intro query present
  exact ⟨tables query present, (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp h).2 query
    (List.mem_of_mem_drop present)⟩

end Airbender.Blake2Round.Proofs
