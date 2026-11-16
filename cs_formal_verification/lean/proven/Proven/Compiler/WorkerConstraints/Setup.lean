module
public import Human.Compiler.WorkerPublicSetup
public import Proven.Compiler.Lookups.NativeRanges
public import Proven.Compiler.Lookups.Clean
public import Proven.KernelRfl

@[expose] public section
namespace Airbender.Compiler.WorkerConstraints
open NativeArithmetic NativeWorkerLookups
set_option warningAsError true

/-- The complete width of a worker's generic tuple, including its table tag. -/
def width : Family → Nat
  | .bigint => 3 | .blakeG => 9 | .blakeRound => 6
  | .columnParity => 8 | .thetaRho => 9 | .chi5 => 11

/-- The source table retains the fixed region for bigint and G, and the full exported trace for the other workers. -/
noncomputable def limit : Family → Nat
  | .bigint => 1390592 | .blakeG => 344896
  | .blakeRound => Blake2Round.blake2RoundSetup.traceLen
  | .columnParity => Keccak.Split.ColumnParity.columnParitySetup.traceLen
  | .thetaRho => Keccak.Split.ThetaRho.thetaRhoSetup.traceLen
  | .chi5 => Keccak.Split.Chi5.chi5Setup.traceLen

/-- The independently interpreted source setup row of each worker. -/
noncomputable def setupRow : (family : Family) → Fin (limit family) → Vector F (width family)
  | .bigint, index => #v[((Bigint.setupRow index).1 : F), ((Bigint.setupRow index).2.1 : F),
      ((Bigint.setupRow index).2.2 : F)]
  | .blakeG, index => (Blake2G.setupRow Blake2G.Control.controllerRows index).map (fun (n : Nat) => (n : F))
  | .blakeRound, index => (Blake2Round.setupRow index.val).map (fun (n : Int) => (n : F))
  | .columnParity, index => (Keccak.Split.setupRow Keccak.Split.ColumnParity.columnParitySetup 8 index.val).map (fun (n : Int) => (n : F))
  | .thetaRho, index => (Keccak.Split.setupRow Keccak.Split.ThetaRho.thetaRhoSetup 9 index.val).map (fun (n : Int) => (n : F))
  | .chi5, index => (Keccak.Split.setupRow Keccak.Split.Chi5.chi5Setup 11 index.val).map (fun (n : Int) => (n : F))

/-- Each worker uses its reviewed description table. -/
noncomputable def setupTable : (family : Family) → Table F (fields (width family))
  | .bigint => Bigint.setupTable
  | .blakeG => Blake2G.setupTable Blake2G.Control.controllerRows
  | .blakeRound => Blake2Round.setupTable
  | .columnParity => Keccak.Split.ColumnParity.setup
  | .thetaRho => Keccak.Split.ThetaRho.setup
  | .chi5 => Keccak.Split.Chi5.setup

/-- Source table membership is equality with one interpreted row. -/
theorem setup_contains (family : Family) (provided : Array (Vector F (width family)))
    (values : Vector F (width family)) :
    (setupTable family).Contains provided values ↔ ∃ index, values = setupRow family index := by
  cases family <;> rfl

/-- Every source setup row fits in the compiled worker trace. -/
theorem setup_fits (family : Family) : limit family ≤ (circuitFor family).trace_len := by
  cases family <;> decide +kernel

/-- Native generic rows retain every source row, followed only by zero padding. -/
theorem native_row (family : Family) (index : Fin (circuitFor family).trace_len) :
    NativeWorkerSetup.rows family 0 index =
      if bound : index.val < limit family then (setupRow family ⟨index.val, bound⟩).toList
      else List.replicate (width family) 0 := by
  have room := index.isLt
  cases family <;> simp only [NativeWorkerSetup.rows, Fin.val_zero, ↓reduceIte]
  all_goals first
    | rfl
    | (dsimp only [NativeWorkerSetup.genericRow, setupRow, limit, width]
       split_ifs with bounded <;> simp_all only [Vector.toList_map, ↓reduceDIte])
  all_goals exact False.elim (bounded index.isLt)

/-- A nonzero table tag excludes native zero padding and gives exactly the reviewed source table. -/
theorem generic_refinement (family : Family) (provided : Array (Vector F (width family)))
    (values : Vector F (width family))
    (tag : (values.toList[width family - 1]?).getD 0 ≠ 0) :
    (∃ index : Fin (circuitFor family).trace_len, values.toList = NativeWorkerSetup.rows family 0 index) ↔
      (setupTable family).Contains provided values := by
  rw [setup_contains]
  constructor
  · rintro ⟨index, same⟩
    rw [native_row] at same
    split at same
    · exact ⟨_, Vector.toList_inj.mp same⟩
    · have zero := congrArg (fun entries : List F => (entries[width family - 1]?).getD 0) same
      have positive : 0 < width family := by cases family <;> decide
      have bounded : width family - 1 < width family := by omega
      simp only [List.getElem?_replicate, bounded, ↓reduceIte, Option.getD_some] at zero
      exact False.elim (tag zero)
  · rintro ⟨index, same⟩
    refine ⟨⟨index.val, index.isLt.trans_le (setup_fits family)⟩, ?_⟩
    rw [native_row, dite_eq_left index.isLt]
    exact congrArg Vector.toList same

/-- An actual generic lookup has exactly the public native table meaning. -/
theorem generic_lookup_refinement (family : Family)
    (expressions : Vector (Airbender.Expression F) (width family)) (logical : Nat → F)
    (tag : (((expressions.map (Verification.environment logical)).toList)[width family - 1]?).getD 0 ≠ 0) :
    (Lookup.mk (setupTable family).toRaw expressions).Contains (Verification.environment logical) ↔
      ∃ index : Fin (circuitFor family).trace_len,
        (expressions.map (Verification.environment logical)).toList = NativeWorkerSetup.rows family 0 index := by
  change (setupTable family).Contains ((Verification.environment logical).data.getTable (setupTable family))
    (expressions.map (Verification.environment logical)) ↔ _
  exact (generic_refinement family _ _ tag).symm

/-- Native scalar range membership gives the canonical source bound. -/
theorem scalar_bound (family : Family) (group : Fin 3) (value : F)
    (member : ∃ index : Fin (circuitFor family).trace_len,
      [value] = NativeWorkerSetup.rows family group index)
    (range : group = 1 ∨ group = 2) :
    value.val < (if group = 1 then 65536 else 524288) := by
  obtain ⟨index, same⟩ := member
  rcases range with rfl | rfl
  · exact NativePublicSetup.Proofs.scalar_bound 65536 (by decide) index.val value same
  · exact NativePublicSetup.Proofs.scalar_bound 524288 (by decide) index.val value same

/-- Each compiled worker trace contains both complete scalar prefixes. -/
theorem scalar_fits (family : Family) : 524288 ≤ (circuitFor family).trace_len := by
  cases family <;> decide +kernel

/-- A canonical scalar value has its public native row. -/
theorem scalar_membership (family : Family) (group : Fin 3) (value : F)
    (range : group = 1 ∨ group = 2)
    (bounded : value.val < (if group = 1 then 65536 else 524288)) :
    ∃ index : Fin (circuitFor family).trace_len,
      [value] = NativeWorkerSetup.rows family group index := by
  rcases range with rfl | rfl
  · change value.val < 65536 at bounded
    refine ⟨⟨value.val, lt_of_lt_of_le (by omega : value.val < 524288) (scalar_fits family)⟩, ?_⟩
    change [value] = [if value.val < 65536 then (value.val : F) else 0]
    rw [ite_eq_left bounded, ZMod.natCast_zmod_val]
  · change value.val < 524288 at bounded
    refine ⟨⟨value.val, bounded.trans_le (scalar_fits family)⟩, ?_⟩
    change [value] = [if value.val < 524288 then (value.val : F) else 0]
    rw [ite_eq_left bounded, ZMod.natCast_zmod_val]

/-- A scalar raw lookup retains the reviewed table membership. -/
theorem scalar_contains (table : Table F field) (expression : Airbender.Expression F) (environment : Environment F) :
    (Lookup.mk table.toRaw #v[expression]).Contains environment ↔
      table.Contains (environment.data.getTable table) (expression.eval environment) := by
  simp only [Lookup.Contains, Table.toRaw, ProverData.getTable,
    Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil]
  rfl

/-- The native 16-bit table and the reviewed scalar lookup have the same members. -/
theorem range16_refinement (family : Family) (expression : Airbender.Expression F) (logical : Nat → F) :
    (Verification.range16 expression).Contains (Verification.environment logical) ↔
      ∃ index : Fin (circuitFor family).trace_len,
        [expression.eval (Verification.environment logical)] = NativeWorkerSetup.rows family 1 index := by
  rw [show Verification.range16 expression = Lookup.mk Verification.range16Table.toRaw #v[expression] from rfl, scalar_contains]
  change (∃ index : Fin 65536, expression.eval (Verification.environment logical) = (index.val : F)) ↔ _
  constructor
  · rintro ⟨index, same⟩
    apply scalar_membership family 1 _ (Or.inl rfl)
    rw [same, ZMod.val_natCast]
    exact lt_of_le_of_lt (Nat.mod_le _ _) index.isLt
  · intro member
    have bounded := scalar_bound family 1 _ member (Or.inl rfl)
    exact ⟨⟨_, bounded⟩, (ZMod.natCast_zmod_val _).symm⟩

/-- The native timestamp table and the reviewed scalar lookup have the same members. -/
theorem timestamp_refinement (family : Family) (expression : Airbender.Expression F) (logical : Nat → F) :
    (Trace.timestampLookup expression).Contains (Verification.environment logical) ↔
      ∃ index : Fin (circuitFor family).trace_len,
        [expression.eval (Verification.environment logical)] = NativeWorkerSetup.rows family 2 index := by
  rw [show Trace.timestampLookup expression = Lookup.mk Trace.timestampTable.toRaw #v[expression] from rfl, scalar_contains]
  change (∃ index : Fin 524288, expression.eval (Verification.environment logical) = (index.val : F)) ↔ _
  constructor
  · rintro ⟨index, same⟩
    apply scalar_membership family 2 _ (Or.inr rfl)
    rw [same, ZMod.val_natCast]
    exact lt_of_le_of_lt (Nat.mod_le _ _) index.isLt
  · intro member
    have bounded := scalar_bound family 2 _ member (Or.inr rfl)
    exact ⟨⟨_, bounded⟩, (ZMod.natCast_zmod_val _).symm⟩

end Airbender.Compiler.WorkerConstraints
