import Tests.PathGConsumedMessage.Data
import Airbender.Proofs.UnifiedReduced.Setup
import Mathlib.Tactic.IntervalCases

namespace Tests.PathGConsumedMessage
open Airbender Trace Arithmetic Reference.RiscV.Sail Reference.Sail

set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

private def queryAt (queries : List (Lookup (ZMod babyBearModulus))) (index : Nat)
    (environment : _root_.Environment (ZMod babyBearModulus)) : Prop :=
  match queries[index]? with
  | some query => query.Contains environment
  | none => True

private theorem queryAt_getElem (queries : List (Lookup (ZMod babyBearModulus)))
    (index : Nat) (environment : _root_.Environment (ZMod babyBearModulus))
    (bound : index < queries.length) (checked : queryAt queries index environment) :
    (queries[index]'bound).Contains environment := by
  unfold queryAt at checked
  rw [List.getElem?_eq_getElem bound] at checked
  exact checked

/-- ROM rows alone depend on the installed instruction bytes. An actual
non-ROM lookup witness transports to any other public program image. -/
private theorem setup_lookup_transport
    {oldState newState : State} {entry : Vector (Expression (ZMod babyBearModulus)) 10}
    {environment : _root_.Environment (ZMod babyBearModulus)}
    (notRom : entry[9].eval environment ≠ 34)
    (member : (Lookup.mk (UnifiedReduced.Setup.table oldState).toRaw entry).Contains environment) :
    (Lookup.mk (UnifiedReduced.Setup.table newState).toRaw entry).Contains environment := by
  change ∃ index : Fin 2097537, entry.map (Expression.eval environment) =
    (UnifiedReduced.Setup.row oldState index).map (fun n : Nat => (n : ZMod babyBearModulus)) at member
  change ∃ index : Fin 2097537, entry.map (Expression.eval environment) =
    (UnifiedReduced.Setup.row newState index).map (fun n : Nat => (n : ZMod babyBearModulus))
  obtain ⟨index, equal⟩ := member
  have fixed : index.val < 1048961 := by
    by_contra outside
    apply notRom
    have romTag : (UnifiedReduced.Setup.row oldState index)[9] = 34 := by
      unfold UnifiedReduced.Setup.row
      rw [dif_neg outside]
      rfl
    have tag : entry[9].eval environment =
        ((UnifiedReduced.Setup.row oldState index)[9] : ZMod babyBearModulus) := by
      simpa only [Vector.getElem_map] using
        congrArg (fun values : Vector (ZMod babyBearModulus) 10 => values[9]) equal
    simpa only [romTag, Nat.cast_ofNat] using tag
  exact ⟨index, by simpa only [UnifiedReduced.Setup.row, dif_pos fixed] using equal⟩

private def cpuQueries (state : State) : List (Lookup (ZMod babyBearModulus)) :=
  FlatOperation.lookups (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table state))

private theorem cpu_tags (index : Fin 228) :
    ∀ column ∈ ([88, 92, 101, 110, 119] : List Nat),
      PathGLoopNative.machineAssignment .protectedMessage index column ≠ 34 := by
  intro column member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals simp [PathGLoopNative.machineAssignment]
  all_goals split_ifs <;> decide +kernel

private theorem cpu_query_transport {oldState newState : State}
    (assignment : Nat → ZMod babyBearModulus)
    (tags : ∀ column ∈ ([88, 92, 101, 110, 119] : List Nat), assignment column ≠ 34)
    (query : Fin 18)
    (member : queryAt (cpuQueries oldState) query.val
      (Verification.environment assignment)) :
    queryAt (cpuQueries newState) query.val (Verification.environment assignment) := by
  fin_cases query
  all_goals dsimp only [queryAt, cpuQueries, UnifiedReduced.importedConstraints,
    FlatOperation.lookups, List.getElem?_cons_zero, List.getElem?_cons_succ] at member ⊢
  all_goals first
    | exact member
    | refine setup_lookup_transport (newState := newState) ?_ member
  all_goals first
    | simpa [Expression.eval, Verification.environment] using tags 88 (by decide)
    | simpa [Expression.eval, Verification.environment] using tags 92 (by decide)
    | simpa [Expression.eval, Verification.environment] using tags 101 (by decide)
    | simpa [Expression.eval, Verification.environment] using tags 110 (by decide)
    | simpa [Expression.eval, Verification.environment] using tags 119 (by decide)

private theorem setup_zero (state : State) :
    (UnifiedReduced.Setup.table state (p := babyBearModulus)).Contains #[]
      (Vector.replicate 10 0) := by
  change ∃ index : Fin 2097537, Vector.replicate 10 (0 : ZMod babyBearModulus) =
    (UnifiedReduced.Setup.row state index).map (fun n : Nat => (n : ZMod babyBearModulus))
  refine ⟨0, ?_⟩
  rw [UnifiedReduced.Setup.Proofs.row_eq_reference]
  have zeroRow : UnifiedReduced.Setup.referenceRow state 0 =
      #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
    change (Verification.shiftBinopRow (0 : Fin 524545)).set 9
      (UnifiedReduced.Setup.binaryTag (Verification.shiftBinopRow (0 : Fin 524545))[9]) = _
    simp only [Verification.shiftBinopRow_eq_reference]
    decide +kernel
  rw [zeroRow]
  ext column bound
  interval_cases column <;> simp

private theorem setup_zero_lookup
    {entry : Vector (Expression (ZMod babyBearModulus)) 10}
    {assignment : Nat → ZMod babyBearModulus}
    (zero : entry.map (Expression.eval (Verification.environment assignment)) =
      Vector.replicate 10 0) :
    (Lookup.mk (UnifiedReduced.Setup.table before).toRaw entry).Contains
      (Verification.environment assignment) := by
  change (UnifiedReduced.Setup.table before).Contains #[]
    (entry.map (Expression.eval (Verification.environment assignment)))
  rw [zero]
  exact setup_zero before

private theorem cpu_store_query (query : Fin 18) :
    queryAt (cpuQueries before) query.val (Verification.environment (cpuAssignment 226)) := by
  fin_cases query
  all_goals dsimp only [queryAt, cpuQueries, UnifiedReduced.importedConstraints,
    FlatOperation.lookups, List.getElem?_cons_zero, List.getElem?_cons_succ]
  all_goals first
    | (apply Verification.range16_contains; decide +kernel)
    | (apply setup_zero_lookup; decide +kernel)

private theorem cpu_queries (index : Fin 228) :
    ∀ lookup ∈ FlatOperation.lookups
      (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table before)),
      lookup.Contains (Verification.environment (cpuAssignment index)) := by
  rw [List.forall_mem_iff_forall_getElem]
  intro query bound
  have short : query < 18 := by simpa only [UnifiedReduced.lookup_count] using bound
  by_cases changed : index.val = 226
  · have same : index = (226 : Fin 228) := Fin.ext changed
    subst index
    exact queryAt_getElem _ _ _ bound (cpu_store_query ⟨query, short⟩)
  · rw [cpu_unchanged index changed]
    have oldBound : query < (cpuQueries (PathGLoopProgram.before .protectedMessage)).length := by
      change query < 18
      exact short
    have old : queryAt (cpuQueries (PathGLoopProgram.before .protectedMessage)) query
        (Verification.environment (PathGLoopNative.machineAssignment .protectedMessage index)) := by
      unfold queryAt
      rw [List.getElem?_eq_getElem oldBound]
      exact PathGLoopNative.machine_queries .protectedMessage index _
        (List.getElem_mem oldBound)
    exact queryAt_getElem _ _ _ bound
      (cpu_query_transport _ (cpu_tags index) ⟨query, short⟩ old)

private theorem cpu_check_0 :
    PathGLoopNative.gCpuEquationsCheck (cpuAssignment 226)
      (((PathGLoopNative.gCpuPolynomials
        (UnifiedReduced.Setup.table (PathGLoopProgram.before .baseline))).drop 0).take 16) = true := by
  decide +kernel

private theorem cpu_check_16 :
    PathGLoopNative.gCpuEquationsCheck (cpuAssignment 226)
      (((PathGLoopNative.gCpuPolynomials
        (UnifiedReduced.Setup.table (PathGLoopProgram.before .baseline))).drop 16).take 16) = true := by
  decide +kernel

private theorem cpu_check_32 :
    PathGLoopNative.gCpuEquationsCheck (cpuAssignment 226)
      (((PathGLoopNative.gCpuPolynomials
        (UnifiedReduced.Setup.table (PathGLoopProgram.before .baseline))).drop 32).take 16) = true := by
  decide +kernel

private theorem cpu_check_48 :
    PathGLoopNative.gCpuEquationsCheck (cpuAssignment 226)
      (((PathGLoopNative.gCpuPolynomials
        (UnifiedReduced.Setup.table (PathGLoopProgram.before .baseline))).drop 48).take 16) = true := by
  decide +kernel

private theorem cpu_check_64 :
    PathGLoopNative.gCpuEquationsCheck (cpuAssignment 226)
      (((PathGLoopNative.gCpuPolynomials
        (UnifiedReduced.Setup.table (PathGLoopProgram.before .baseline))).drop 64).take 16) = true := by
  decide +kernel

private theorem cpu_check_80 :
    PathGLoopNative.gCpuEquationsCheck (cpuAssignment 226)
      (((PathGLoopNative.gCpuPolynomials
        (UnifiedReduced.Setup.table (PathGLoopProgram.before .baseline))).drop 80).take 16) = true := by
  decide +kernel

private theorem cpu_check_96 :
    PathGLoopNative.gCpuEquationsCheck (cpuAssignment 226)
      (((PathGLoopNative.gCpuPolynomials
        (UnifiedReduced.Setup.table (PathGLoopProgram.before .baseline))).drop 96).take 16) = true := by
  decide +kernel

private theorem cpu_check_112 :
    PathGLoopNative.gCpuEquationsCheck (cpuAssignment 226)
      (((PathGLoopNative.gCpuPolynomials
        (UnifiedReduced.Setup.table (PathGLoopProgram.before .baseline))).drop 112).take 16) = true := by
  decide +kernel

private theorem cpu_check_128 :
    PathGLoopNative.gCpuEquationsCheck (cpuAssignment 226)
      (((PathGLoopNative.gCpuPolynomials
        (UnifiedReduced.Setup.table (PathGLoopProgram.before .baseline))).drop 128).take 1) = true := by
  decide +kernel

private theorem cpu_store_equations
    (setup : Table (ZMod babyBearModulus) (fields 10)) :
    ∀ expression ∈ FlatOperation.constraints (UnifiedReduced.importedConstraints setup),
      expression.eval (Verification.environment (cpuAssignment 226)) = 0 := by
  rw [List.forall_mem_iff_forall_getElem]
  intro equation bound
  have actual : equation < 129 := by simpa only [UnifiedReduced.constraint_count] using bound
  change ((PathGLoopNative.gCpuPolynomials setup)[equation]'bound).eval _ = 0
  by_cases below : equation < 16
  · exact PathGLoopNative.g_cpu_equations_of_check (cpuAssignment 226) setup
      0 16 equation (by omega) (by omega) actual cpu_check_0
  · by_cases below : equation < 32
    · exact PathGLoopNative.g_cpu_equations_of_check (cpuAssignment 226) setup
        16 16 equation (by omega) (by omega) actual cpu_check_16
    · by_cases below : equation < 48
      · exact PathGLoopNative.g_cpu_equations_of_check (cpuAssignment 226) setup
          32 16 equation (by omega) (by omega) actual cpu_check_32
      · by_cases below : equation < 64
        · exact PathGLoopNative.g_cpu_equations_of_check (cpuAssignment 226) setup
            48 16 equation (by omega) (by omega) actual cpu_check_48
        · by_cases below : equation < 80
          · exact PathGLoopNative.g_cpu_equations_of_check (cpuAssignment 226) setup
              64 16 equation (by omega) (by omega) actual cpu_check_64
          · by_cases below : equation < 96
            · exact PathGLoopNative.g_cpu_equations_of_check (cpuAssignment 226) setup
                80 16 equation (by omega) (by omega) actual cpu_check_80
            · by_cases below : equation < 112
              · exact PathGLoopNative.g_cpu_equations_of_check (cpuAssignment 226) setup
                  96 16 equation (by omega) (by omega) actual cpu_check_96
              · by_cases below : equation < 128
                · exact PathGLoopNative.g_cpu_equations_of_check (cpuAssignment 226) setup
                    112 16 equation (by omega) (by omega) actual cpu_check_112
                · exact PathGLoopNative.g_cpu_equations_of_check (cpuAssignment 226) setup
                      128 1 equation (by omega) (by omega) actual cpu_check_128

theorem cpu_core (index : Fin 228) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (cpuAssignment index))
      (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table before)) := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  refine ⟨?_, cpu_queries index⟩
  by_cases changed : index.val = 226
  · have same : index = (226 : Fin 228) := Fin.ext changed
    subst index
    exact cpu_store_equations _
  · rw [cpu_unchanged index changed]
    exact PathGLoopNative.machine_equations .protectedMessage index _

theorem cpu_timestamps (index : Fin 228) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (cpuAssignment index))
      UnifiedReduced.importedConstraintsTimestampLookups := by
  by_cases changed : index.val = 226
  · have same : index = (226 : Fin 228) := Fin.ext changed
    subst index
    rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
    constructor
    · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
    · rw [List.forall_mem_iff_forall_getElem]
      intro query bound
      have short : query < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
      have old := Verification.lookup_of_holds
        (PathGLoopNative.machine_timestamps .protectedMessage 226) ⟨query, bound⟩
      interval_cases query
      all_goals first
        | exact old
        | (apply Trace.Proofs.range_contains; decide +kernel)
  · rw [cpu_unchanged index changed]
    exact PathGLoopNative.machine_timestamps .protectedMessage index

private def workerIndices : Vector Nat 19 :=
  #v[344823, 7, 0, 0, 0, 65536, 82240, 65600, 65543, 82240,
    65600, 119, 0, 1792, 0, 80192, 82254, 65863, 82478]

private theorem worker_index_bound (index : Fin 19) : workerIndices[index] < 344896 := by
  fin_cases index <;> decide

private theorem worker_final_table_query (query : Fin 19) :
    ((FlatOperation.lookups (Blake2G.importedConstraints
      (Blake2G.setupTable Blake2G.Control.controllerRows))).get
        ⟨query.val + 2, by rw [Blake2G.lookup_count]; have := query.isLt; omega⟩).Contains
      (Verification.environment (workerAssignment 55)) := by
  let selected : Fin 344896 := ⟨workerIndices[query], worker_index_bound query⟩
  fin_cases query
  all_goals refine ⟨selected, ?_⟩
  all_goals simp only [Blake2G.Proofs.setup_row_characterization]
  all_goals apply Vector.ext
  all_goals intro column bound
  all_goals change column < 9 at bound
  all_goals interval_cases column
  all_goals simp only [Vector.getElem_map]
  all_goals decide +kernel +revert

private theorem worker_final_equations :
    (FlatOperation.constraints (Blake2G.importedConstraints
      (Blake2G.setupTable Blake2G.Control.controllerRows))).all
      (fun expression => decide
        (expression.eval (Verification.environment (workerAssignment 55)) = 0)) = true := by
  decide +kernel

private theorem worker_final_core :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (workerAssignment 55))
      (Blake2G.importedConstraints (Blake2G.setupTable Blake2G.Control.controllerRows)) := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · intro expression member
    exact of_decide_eq_true (List.all_eq_true.mp worker_final_equations expression member)
  · rw [List.forall_mem_iff_forall_getElem]
    intro query bound
    have short : query < 21 := by simpa only [Blake2G.lookup_count] using bound
    by_cases alignment : query < 2
    · interval_cases query
      all_goals apply Trace.Proofs.range_contains
      all_goals decide +kernel
    · have source := worker_final_table_query ⟨query - 2, by omega⟩
      have position : query - 2 + 2 = query := by omega
      simpa only [List.get_eq_getElem, Fin.val_mk, position] using source

theorem worker_core (index : Fin 56) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (workerAssignment index))
      (Blake2G.importedConstraints (Blake2G.setupTable Blake2G.Control.controllerRows)) := by
  by_cases changed : index.val = 55
  · have same : index = (55 : Fin 56) := Fin.ext changed
    subst index
    exact worker_final_core
  · rw [worker_unchanged index changed, FlatOperation.constraintsHoldFlat_iff_forall_mem]
    exact ⟨PathGLoopNative.worker_equations .protectedMessage index,
      PathGLoopNative.worker_queries .protectedMessage index⟩

theorem worker_timestamps (index : Fin 56) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (workerAssignment index))
      Blake2G.importedConstraintsTimestampLookups := by
  by_cases changed : index.val = 55
  · have same : index = (55 : Fin 56) := Fin.ext changed
    subst index
    rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
    constructor
    · simp [Blake2G.importedConstraintsTimestampLookups, FlatOperation.constraints]
    · rw [List.forall_mem_iff_forall_getElem]
      intro query bound
      have short : query < 21 := by simpa only [Blake2G.timestamp_count] using bound
      have old := Verification.lookup_of_holds
        (PathGLoopNative.worker_timestamps .protectedMessage 55) ⟨query, bound⟩
      interval_cases query
      all_goals first
        | exact old
        | (apply Trace.Proofs.range_contains; decide +kernel)
  · rw [worker_unchanged index changed]
    exact PathGLoopNative.worker_timestamps .protectedMessage index

end Tests.PathGConsumedMessage
