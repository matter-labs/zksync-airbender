import Airbender.Review.Circuits.Blake2Round.Tables.Setup
import Airbender.Review.Circuits.Blake2Round.Artifact
import Airbender.Review.Helpers.Properties
import Airbender.Proofs.Blake2G.Tables
import Airbender.Proofs.Blake2Round.ImportedXor
import Airbender.Proofs.Constraints
import Mathlib.Tactic.IntervalCases

namespace Airbender.Blake2Round.Proofs

set_option maxRecDepth 16384
set_option maxHeartbeats 1200000

private theorem padded_row (i : Fin 344384) :
    Blake2G.setupRow (fun _ => Vector.replicate 7 0)
      ⟨i.val, by have size := i.isLt; omega⟩ =
    #v[(setupRow i)[0], (setupRow i)[1], (setupRow i)[2], 0, 0, 0, 0, 0, (setupRow i)[3]] := by
  have size := i.isLt
  simp only [Blake2G.Proofs.setup_row_characterization, setup_row_characterization]
  unfold Blake2G.referenceSetupRow
  dsimp only
  split_ifs <;> simp [Blake2G.xorRow]

def padXor {F : Type} [Zero F] (row : Vector F 4) : Vector F 9 :=
  #v[row[0], row[1], row[2], 0, 0, 0, 0, 0, row[3]]

/-- Transfer actual four-column membership to the G fragment's nine-column
    schema, possibly in a different environment. All evaluated columns agree. -/
theorem padded_membership {p : Nat} [Fact p.Prime]
    {source : Vector (Expression (ZMod p)) 4} {target : Vector (Expression (ZMod p)) 9}
    {sourceEnv targetEnv : Environment (ZMod p)}
    (h : (Lookup.mk setupTable.toRaw source).Contains sourceEnv)
    (columns : target.map (Expression.eval targetEnv) = padXor (source.map (Expression.eval sourceEnv))) :
    (Lookup.mk (Blake2G.setupTable (fun _ => Vector.replicate 7 0)).toRaw target).Contains targetEnv := by
  change ∃ i : Fin 344384, source.map (Expression.eval sourceEnv) =
    (setupRow i).map (fun (n : Nat) => (n : ZMod p)) at h
  obtain ⟨i, row⟩ := h
  change ∃ j : Fin 344896, target.map (Expression.eval targetEnv) =
    (Blake2G.setupRow (fun _ => Vector.replicate 7 0) j).map (fun (n : Nat) => (n : ZMod p))
  refine ⟨⟨i.val, by have size := i.isLt; omega⟩, ?_⟩
  rw [columns, row, padded_row]
  ext j hj
  interval_cases j <;> simp [padXor]

/-- Four-column membership reuses the checked G XOR theorem by padding the
    same table row. There is one XOR semantics, supplied by native Clean lookups. -/
theorem xor_lookup {p : Nat} [Fact p.Prime] (hp : 512 ≤ p)
    {entry : Vector (Expression (ZMod p)) 4} {env : Environment (ZMod p)}
    (kind : Fin 5) (h : (Lookup.mk setupTable.toRaw entry).Contains env)
    (selected : entry[3].eval env = ((#v[4, 17, 18, 19, 20][kind] : Nat) : ZMod p)) :
    (entry[0].eval env).val < 2 ^ (#v[8, 3, 4, 7, 9][kind]) ∧
    (entry[1].eval env).val < 2 ^ (#v[8, 3, 4, 7, 9][kind]) ∧
    (entry[2].eval env).val < 2 ^ (#v[8, 3, 4, 7, 9][kind]) ∧
    (entry[2].eval env).val = (entry[0].eval env).val ^^^ (entry[1].eval env).val := by
  change ∃ i : Fin 344384, entry.map (Expression.eval env) =
    (setupRow i).map (fun (n : Nat) => (n : ZMod p)) at h
  obtain ⟨i, row⟩ := h
  let padded : Vector (Expression (ZMod p)) 9 :=
    #v[entry[0], entry[1], entry[2], .const 0, .const 0, .const 0, .const 0, .const 0, entry[3]]
  have member : (Lookup.mk (Blake2G.setupTable (fun _ => Vector.replicate 7 0)).toRaw padded).Contains env := by
    change ∃ j : Fin 344896, padded.map (Expression.eval env) =
      (Blake2G.setupRow (fun _ => Vector.replicate 7 0) j).map (fun (n : Nat) => (n : ZMod p))
    refine ⟨⟨i.val, by have size := i.isLt; omega⟩, ?_⟩
    rw [padded_row]
    have column (j : Fin 4) := congrArg (fun v : Vector (ZMod p) 4 => v[j]) row
    ext j hj
    interval_cases j <;> simp [padded, Expression.eval]
    all_goals first
      | simpa using column 0
      | simpa using column 1
      | simpa using column 2
      | simpa using column 3
  simpa [padded] using Blake2G.Proofs.xor_lookup hp kind member (by simpa [padded] using selected)

/-- Reuse the typed theorem for a native Clean lookup with the same table.
    Eliminating the table equality also identifies the entry's four-column type. -/
theorem xor_lookup_raw {p : Nat} [Fact p.Prime] (hp : 512 ≤ p)
    {query : Lookup (ZMod p)} {env : Environment (ZMod p)} (kind : Fin 5)
    (h : query.Contains env) (table : query.table = setupTable.toRaw)
    (selected : (query.entry.toArray[3]!).eval env =
      ((#v[4, 17, 18, 19, 20][kind] : Nat) : ZMod p)) :
    (query.entry.toArray[0]!.eval env).val < 2 ^ (#v[8, 3, 4, 7, 9][kind]) ∧
    (query.entry.toArray[1]!.eval env).val < 2 ^ (#v[8, 3, 4, 7, 9][kind]) ∧
    (query.entry.toArray[2]!.eval env).val < 2 ^ (#v[8, 3, 4, 7, 9][kind]) ∧
    (query.entry.toArray[2]!.eval env).val =
      (query.entry.toArray[0]!.eval env).val ^^^ (query.entry.toArray[1]!.eval env).val := by
  rcases query with ⟨raw, entry⟩
  cases table
  have get (j : Nat) (hj : j < 4) : entry.toArray[j]! = entry[j] := by
    rw [getElem!_pos entry.toArray j (by
      rw [entry.size_toArray]
      change j < size (fields 4)
      rw [show size (fields 4) = 4 from rfl]
      exact hj)]
    rfl
  simpa only [get 0 (by decide), get 1 (by decide), get 2 (by decide)] using
    xor_lookup hp kind h (by simpa only [get 3 (by decide)] using selected)

private theorem row_tag (i : Fin 344384) :
    ∃ kind : Fin 5, (setupRow i)[3] = (#v[4, 17, 18, 19, 20][kind] : Nat) := by
  have size := i.isLt
  simp only [setup_row_characterization]
  unfold Blake2G.referenceSetupRow
  dsimp only
  split_ifs
  all_goals simp only [Blake2G.xorRow, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals first
    | omega
    | exact ⟨0, rfl⟩
    | exact ⟨1, rfl⟩
    | exact ⟨2, rfl⟩
    | exact ⟨3, rfl⟩
    | exact ⟨4, rfl⟩

/-- Every row in this setup is a valid tagged XOR row. Its membership supplies
    the tag/width as well as XOR; no separate per-query tag premise is needed. -/
theorem xor_lookup_any {p : Nat} [Fact p.Prime] (hp : 512 ≤ p)
    {entry : Vector (Expression (ZMod p)) 4} {env : Environment (ZMod p)}
    (h : (Lookup.mk setupTable.toRaw entry).Contains env) :
    ∃ kind : Fin 5,
      entry[3].eval env = ((#v[4, 17, 18, 19, 20][kind] : Nat) : ZMod p) ∧
      (entry[0].eval env).val < 2 ^ (#v[8, 3, 4, 7, 9][kind]) ∧
      (entry[1].eval env).val < 2 ^ (#v[8, 3, 4, 7, 9][kind]) ∧
      (entry[2].eval env).val < 2 ^ (#v[8, 3, 4, 7, 9][kind]) ∧
      (entry[2].eval env).val = (entry[0].eval env).val ^^^ (entry[1].eval env).val := by
  have rows := h
  change ∃ i : Fin 344384, entry.map (Expression.eval env) =
    (setupRow i).map (fun (n : Nat) => (n : ZMod p)) at rows
  obtain ⟨i, row⟩ := rows
  obtain ⟨kind, tag⟩ := row_tag i
  have selected : entry[3].eval env = ((#v[4, 17, 18, 19, 20][kind] : Nat) : ZMod p) := by
    have column := congrArg (fun v : Vector (ZMod p) 4 => v[3]) row
    simpa only [Vector.getElem_map, tag] using column
  exact ⟨kind, selected, xor_lookup hp kind h selected⟩

/-- Every imported query supplies its tagged chunk bounds and exact XOR,
    including all eight G invocations and final-output queries. -/
theorem data_lookups {p : Nat} [Fact p.Prime] (hp : 512 ≤ p) {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    ∀ query ∈ (FlatOperation.lookups (importedConstraints setupTable)).drop 2,
      ∃ kind : Fin 5,
        (query.entry.toArray[3]!).eval (Verification.environment w) =
          ((#v[4, 17, 18, 19, 20][kind] : Nat) : ZMod p) ∧
        (query.entry.toArray[0]!.eval (Verification.environment w)).val < 2 ^ (#v[8, 3, 4, 7, 9][kind]) ∧
        (query.entry.toArray[1]!.eval (Verification.environment w)).val < 2 ^ (#v[8, 3, 4, 7, 9][kind]) ∧
        (query.entry.toArray[2]!.eval (Verification.environment w)).val < 2 ^ (#v[8, 3, 4, 7, 9][kind]) ∧
        (query.entry.toArray[2]!.eval (Verification.environment w)).val =
          (query.entry.toArray[0]!.eval (Verification.environment w)).val ^^^
            (query.entry.toArray[1]!.eval (Verification.environment w)).val := by
  have tables : ∀ query ∈ (FlatOperation.lookups (importedConstraints (p := p) setupTable)).drop 2,
      query.table = setupTable.toRaw := by
    dsimp only [importedConstraints, FlatOperation.lookups, List.drop]
    simp only [List.forall_mem_cons, true_and]
    exact List.forall_mem_nil _
  intro query present
  have table := tables query present
  have member := (FlatOperation.constraintsHoldFlat_iff_forall_mem.mp h).2 query
    (List.mem_of_mem_drop present)
  rcases query with ⟨raw, entry⟩
  cases table
  have get (j : Nat) (hj : j < 4) : entry.toArray[j]! = entry[j] := by
    rw [getElem!_pos entry.toArray j (by
      rw [entry.size_toArray]
      change j < size (fields 4)
      rw [show size (fields 4) = 4 from rfl]
      exact hj)]
    rfl
  simpa only [get 0 (by decide), get 1 (by decide), get 2 (by decide), get 3 (by decide)] using
    xor_lookup_any hp member

end Airbender.Blake2Round.Proofs
