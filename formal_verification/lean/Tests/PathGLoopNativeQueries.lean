import Tests.PathGLoopNativeBase

namespace Tests.PathGLoopNative
open Airbender Trace Arithmetic Reference.RiscV.Sail Reference.Sail PathGLoopProgram
set_option warningAsError true
set_option Elab.async false

/- Native range, setup, timestamp, public decoding and request checks for the
   concrete G loop traces. -/

/-- Optional selection keeps list bounds out of native expression reduction. -/
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

private theorem query_unified_row (state : State) (query : Vector (ZMod babyBearModulus) 10)
    (index : Fin 2097537)
    (same : query = (UnifiedReduced.Setup.referenceRow state index).map
      (fun value : Nat => (value : ZMod babyBearModulus))) :
    (UnifiedReduced.Setup.table state).Contains #[] query := by
  change ∃ row : Fin 2097537, query = (UnifiedReduced.Setup.row state row).map
    (fun value : Nat => (value : ZMod babyBearModulus))
  refine ⟨index, ?_⟩
  rw [UnifiedReduced.Setup.Proofs.row_eq_reference]
  exact same

private theorem query_unified_zero_lookup (state : State) :
    (UnifiedReduced.Setup.table state (p := babyBearModulus)).Contains #[]
      (Vector.replicate 10 0) := by
  have zeroRow : UnifiedReduced.Setup.referenceRow state 0 =
      #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
    change (Verification.shiftBinopRow (0 : Fin 524545)).set 9
      (UnifiedReduced.Setup.binaryTag (Verification.shiftBinopRow (0 : Fin 524545))[9]) = _
    simp only [Verification.shiftBinopRow_eq_reference]
    decide +kernel
  apply query_unified_row state _ 0
  rw [zeroRow]
  ext column bound
  interval_cases column <;> simp

private theorem query_unified_reg_zero_lookup (state : State) (value : Nat)
    (bound : value < 131072) :
    (UnifiedReduced.Setup.table state (p := babyBearModulus)).Contains #[]
      #v[value, (if value = 0 then 1 else 0 : Nat), 0, 0, 0, 0, 0, 0, 0, 1] := by
  apply query_unified_row state _ ⟨524545 + value, by omega⟩
  have fixed : 524545 + value < 1048961 := by omega
  have binary : ¬524545 + value < 524545 := by omega
  have zero : 524545 + value < 655617 := by omega
  simp only [UnifiedReduced.Setup.referenceRow, fixed, ↓reduceDIte,
    UnifiedReduced.Setup.referenceFixedRow, binary, zero, ↓reduceIte,
    show 524545 + value - 524545 = value by omega]
  ext column size
  interval_cases column <;> simp

private theorem query_unified_positive_sign_lookup (state : State) :
    (UnifiedReduced.Setup.table state (p := babyBearModulus)).Contains #[]
      #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 5] := by
  have signRow : UnifiedReduced.Setup.referenceRow state 655617 =
      #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 5] := by
    rfl
  apply query_unified_row state _ 655617
  rw [signRow]
  ext column bound
  interval_cases column <;> simp

/-- A closed three-key scalar check, independent of public state and local
Fin-bound proofs. It evaluates only the mathematical conditional row. -/
private theorem query_conditional_value : ∀ kind : Fin 3,
    Verification.conditionalValue (UnifiedReduced.Setup.conditionalKey
      (#v[0, 16, 24][kind] : Nat)) = (#v[0, 1, 0][kind] : Nat) := by
  decide +kernel

private theorem query_unified_conditional_lookup (state : State) (kind : Fin 3) :
    (UnifiedReduced.Setup.table state (p := babyBearModulus)).Contains #[]
      #v[(#v[0, 16, 24][kind] : Nat), (#v[0, 1, 0][kind] : Nat),
        0, 0, 0, 0, 0, 0, 0, 51] := by
  have conditionalRow : UnifiedReduced.Setup.referenceRow state
      ⟨786689 + (#v[0, 16, 24][kind] : Nat), by fin_cases kind <;> decide⟩ =
      #v[(#v[0, 16, 24][kind] : Nat), (#v[0, 1, 0][kind] : Nat),
        0, 0, 0, 0, 0, 0, 0, 51] := by
    have keyBound : (#v[0, 16, 24][kind] : Nat) < 128 := by
      fin_cases kind <;> decide
    have fixed : 786689 + (#v[0, 16, 24][kind] : Nat) < 1048961 := by omega
    have binary : ¬786689 + (#v[0, 16, 24][kind] : Nat) < 524545 := by omega
    have zero : ¬786689 + (#v[0, 16, 24][kind] : Nat) < 655617 := by omega
    have sign : ¬786689 + (#v[0, 16, 24][kind] : Nat) < 721153 := by omega
    have cleanup : ¬786689 + (#v[0, 16, 24][kind] : Nat) < 786689 := by omega
    have conditional : 786689 + (#v[0, 16, 24][kind] : Nat) < 786817 := by omega
    simp only [UnifiedReduced.Setup.referenceRow, fixed, ↓reduceDIte,
      UnifiedReduced.Setup.referenceFixedRow, binary, zero, sign, cleanup, conditional,
      ↓reduceIte, show 786689 + (#v[0, 16, 24][kind] : Nat) - 786689 =
        (#v[0, 16, 24][kind] : Nat) by omega]
    change (#v[(#v[0, 16, 24][kind] : Nat),
      Verification.conditionalValue (UnifiedReduced.Setup.conditionalKey
        (#v[0, 16, 24][kind] : Nat)), 0, 0, 0, 0, 0, 0, 0, 51] : Vector Nat 10) =
      #v[(#v[0, 16, 24][kind] : Nat), (#v[0, 1, 0][kind] : Nat),
        0, 0, 0, 0, 0, 0, 0, 51]
    exact congrArg (fun result : Nat =>
      (#v[(#v[0, 16, 24][kind] : Nat), result, 0, 0, 0, 0, 0, 0, 0, 51] : Vector Nat 10))
      (query_conditional_value kind)
  apply query_unified_row state _
    ⟨786689 + (#v[0, 16, 24][kind] : Nat), by fin_cases kind <;> decide⟩
  rw [conditionalRow]
  ext column bound
  interval_cases column <;> simp

private theorem query_unified_cleanup_lookup (state : State) (address : Nat)
    (bound : address < 65536) (aligned : address % 4 = 0) :
    (UnifiedReduced.Setup.table state (p := babyBearModulus)).Contains #[]
      #v[address, 0, address, 0, 0, 0, 0, 0, 0, 2] := by
  apply query_unified_row state _ ⟨721153 + address, by omega⟩
  have fixed : 721153 + address < 1048961 := by omega
  have binary : ¬721153 + address < 524545 := by omega
  have zero : ¬721153 + address < 655617 := by omega
  have sign : ¬721153 + address < 721153 := by omega
  have cleanup : 721153 + address < 786689 := by omega
  have bit : address / 2 % 2 = 0 := by omega
  simp only [UnifiedReduced.Setup.referenceRow, fixed, ↓reduceDIte,
    UnifiedReduced.Setup.referenceFixedRow, binary, zero, sign, cleanup, ↓reduceIte,
    show 721153 + address - 721153 = address by omega, bit, aligned, Nat.sub_zero]
  ext column size
  interval_cases column <;> simp

/-- Transport only a vector equality into an already proved real setup row. -/
private theorem query_pooled_of_eq {state : State} {query expected : Vector (ZMod babyBearModulus) 10}
    (member : (UnifiedReduced.Setup.table state).Contains #[] expected)
    (same : query = expected) : (UnifiedReduced.Setup.table state).Contains #[] query := by
  rw [same]
  exact member

private noncomputable def gMachineQueries (variant : Variant) : List (Lookup (ZMod babyBearModulus)) :=
  FlatOperation.lookups (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table (before variant)))

private theorem g_machine_query_count (variant : Variant) : (gMachineQueries variant).length = 18 := by rfl

private theorem boot_machine_query (variant : Variant) (index : Fin 6) (slot : Nat) (slotBound : slot < 18) :
    queryAt (gMachineQueries variant) slot
        (Verification.environment
          (machineAssignment variant ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩)) := by
  by_cases range : slot < 13
  · interval_cases slot
    all_goals dsimp only [queryAt, gMachineQueries, UnifiedReduced.importedConstraints,
      FlatOperation.lookups, List.getElem?_cons_zero, List.getElem?_cons_succ]
    all_goals apply Verification.range16_contains
    all_goals fin_cases index <;> cases variant <;> decide +kernel
  · have pooled : 13 ≤ slot := by omega
    interval_cases slot
    all_goals dsimp only [queryAt, gMachineQueries, UnifiedReduced.importedConstraints,
      FlatOperation.lookups, List.getElem?_cons_zero, List.getElem?_cons_succ]
    all_goals dsimp only [Lookup.Contains, Table.toRaw, Verification.environment, fromElements]
    all_goals rw [Array.map_empty]
    all_goals change (UnifiedReduced.Setup.table (before variant)).Contains #[] _
    all_goals fin_cases index
    all_goals solve
      | (apply query_pooled_of_eq (query_unified_zero_lookup (before variant));
          cases variant <;> decide +kernel)
      | (apply query_pooled_of_eq (query_unified_reg_zero_lookup (before variant) 24 (by decide));
          cases variant <;> decide +kernel)
      | (apply query_pooled_of_eq (query_unified_positive_sign_lookup (before variant));
          cases variant <;> decide +kernel)
      | (apply query_pooled_of_eq (query_unified_conditional_lookup (before variant) 0);
          cases variant <;> decide +kernel)
      | (apply query_pooled_of_eq (query_unified_cleanup_lookup (before variant) 128 (by decide) (by decide));
          cases variant <;> decide +kernel)

private def queryRangeColumns : Vector Nat 13 :=
  #v[78, 79, 50, 51, 1, 81, 38, 39, 44, 45, 86, 30, 31]

private theorem query_range_nat (value : Nat) (bound : value < 65536) :
    (value : ZMod babyBearModulus).val < 65536 := by
  have canonical : value < babyBearModulus := by dsimp [babyBearModulus]; omega
  rw [ZMod.val_natCast_of_lt canonical]
  exact bound

/-- The thirteen real imported range queries need only these scalar bounds. -/
private theorem machine_ranges_of_bounds (variant : Variant)
    (assignment : Nat → ZMod babyBearModulus)
    (bounded : ∀ column : Fin 13, (assignment queryRangeColumns[column]).val < 65536)
    (slot : Nat) (slotBound : slot < 13) :
    queryAt (gMachineQueries variant) slot (Verification.environment assignment) := by
  interval_cases slot
  all_goals dsimp only [queryAt, gMachineQueries, UnifiedReduced.importedConstraints,
    FlatOperation.lookups, List.getElem?_cons_zero, List.getElem?_cons_succ]
  all_goals apply Verification.range16_contains
  · simpa [Expression.eval, Verification.environment, queryRangeColumns, limbBase] using bounded 0
  · simpa [Expression.eval, Verification.environment, queryRangeColumns, limbBase] using bounded 1
  · simpa [Expression.eval, Verification.environment, queryRangeColumns, limbBase] using bounded 2
  · simpa [Expression.eval, Verification.environment, queryRangeColumns, limbBase] using bounded 3
  · simpa [Expression.eval, Verification.environment, queryRangeColumns, limbBase] using bounded 4
  · simpa [Expression.eval, Verification.environment, queryRangeColumns, limbBase] using bounded 5
  · simpa [Expression.eval, Verification.environment, queryRangeColumns, limbBase] using bounded 6
  · simpa [Expression.eval, Verification.environment, queryRangeColumns, limbBase] using bounded 7
  · simpa [Expression.eval, Verification.environment, queryRangeColumns, limbBase] using bounded 8
  · simpa [Expression.eval, Verification.environment, queryRangeColumns, limbBase] using bounded 9
  · simpa [Expression.eval, Verification.environment, queryRangeColumns, limbBase] using bounded 10
  · simpa [Expression.eval, Verification.environment, queryRangeColumns, limbBase] using bounded 11
  · simpa [Expression.eval, Verification.environment, queryRangeColumns, limbBase] using bounded 12

private theorem query_code_pc_bound (variant : Variant) (entry : Fin 12) :
    (codeEntry variant entry).pc.toNat + 4 < 65536 := by
  fin_cases entry <;> cases variant <;> decide +kernel

private theorem query_next_pc_bound (index : Fin 228) : nextPC index < 65536 := by
  have checked : (List.finRange 228).all (fun row => decide (nextPC row < 65536)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp checked index (List.mem_finRange index))

/-- Only the native range coordinates are projected; decoder words and the
chronological memory ledger remain opaque. -/
private def loopRangeValue (variant : Variant) (index : Fin 55) (phase : Fin 4)
    (slot : Fin 13) : Nat :=
  let row := gapRow index phase
  let saved := if isBranch row then source0 variant row
    else (codeEntry variant (rowCodeIndex row)).pc.toNat + 4
  #v[if isBranch row || isJal row then saved else 0, 0,
    newDestination variant row % 65536, newDestination variant row / 65536, 0,
    if isBranch row || isJal row then nextPC row else 0,
    if isCaller row then 0x7c8 else (metadata variant row).rs2.toNat,
    0, (metadata variant row).rd.toNat, 0, 0, nextPC row, 0][slot]

private theorem loop_range_coordinate (variant : Variant) (index : Fin 55) (phase : Fin 4)
    (slot : Fin 13) :
    machineAssignment variant (gapRow index phase) queryRangeColumns[slot] =
      (loopRangeValue variant index phase slot : ZMod babyBearModulus) := by
  have notStore : isStore variant (gapRow index phase) = false := by
    have indexBound := index.isLt
    have phaseBound := phase.isLt
    have different : (gapRow index phase).val ≠ 226 := by dsimp [gapRow]; omega
    simp [isStore, different]
  fin_cases slot
  all_goals simp [queryRangeColumns, loopRangeValue, machineAssignment, notStore,
    Nat.cast_ite, Nat.cast_add]

private theorem loop_range_value_bound (variant : Variant) (index : Fin 55) (phase : Fin 4)
    (slot : Fin 13) : loopRangeValue variant index phase slot < 65536 := by
  have indexBound := index.isLt
  have phaseBound := phase.isLt
  have lower : 6 ≤ (gapRow index phase).val := by dsimp [gapRow]; omega
  have upper : (gapRow index phase).val < 226 := by dsimp [gapRow]; omega
  have sourceBound : source0 variant (gapRow index phase) < 65536 := by
    unfold source0
    split_ifs <;> omega
  have outputBound : newDestination variant (gapRow index phase) < 65536 := by
    unfold newDestination
    split_ifs <;> omega
  have pcBound := query_code_pc_bound variant (rowCodeIndex (gapRow index phase))
  have nextBound := query_next_pc_bound (gapRow index phase)
  have sourceRegister := (metadata variant (gapRow index phase)).rs2.isLt
  have destinationRegister := (metadata variant (gapRow index phase)).rd.isLt
  fin_cases slot
  all_goals simp [loopRangeValue, Nat.mod_eq_of_lt outputBound, Nat.div_eq_of_lt outputBound]
  all_goals first
    | omega
    | (split_ifs <;> omega)

private theorem loop_range_bounded (variant : Variant) (index : Fin 55) (phase : Fin 4)
    (slot : Fin 13) :
    (machineAssignment variant (gapRow index phase) queryRangeColumns[slot]).val < 65536 := by
  rw [loop_range_coordinate]
  exact query_range_nat _ (loop_range_value_bound variant index phase slot)

/-- The pooled-query scratch coordinates are just gates, saved values and the
next PC. This stencil is connected to every actual queried column below. -/
private def pooledAssignment (family branch taken : Bool) (saved pc : Nat)
    (column : Nat) : ZMod babyBearModulus :=
  if column = 88 then if family then 1 else 0
  else if column = 89 then if family then saved else 0
  else if column = 90 then if branch && !taken then 1 else 0
  else if column = 92 ∨ column = 101 then if family then 5 else 0
  else if column = 110 then if family then 51 else 0
  else if column = 111 then if branch then if taken then 16 else 24 else 0
  else if column = 112 then if taken then 1 else 0
  else if column = 119 then if family then 2 else 0
  else if column = 120 ∨ column = 122 then if family then pc else 0
  else 0

private def loopPooledAssignment (variant : Variant) (index : Fin 55) (phase : Fin 4) :
    Nat → ZMod babyBearModulus :=
  let row := gapRow index phase
  pooledAssignment (isBranch row || isJal row) (isBranch row)
    (isBranch row && decide (iteration row < 54))
    (if isBranch row then source0 variant row
      else (codeEntry variant (rowCodeIndex row)).pc.toNat + 4) (nextPC row)

private theorem loop_pooled_coordinate (variant : Variant) (index : Fin 55) (phase : Fin 4)
    (column : Nat) (lower : 86 ≤ column) (upper : column ≤ 127) :
    machineAssignment variant (gapRow index phase) column =
      loopPooledAssignment variant index phase column := by
  have notStore : isStore variant (gapRow index phase) = false := by
    have indexBound := index.isLt
    have phaseBound := phase.isLt
    have different : (gapRow index phase).val ≠ 226 := by dsimp [gapRow]; omega
    simp [isStore, different]
  interval_cases column
  all_goals simp [machineAssignment, loopPooledAssignment, pooledAssignment, notStore]

private theorem query_environment_get (assignment : Nat → ZMod babyBearModulus)
    (column : Nat) : (Verification.environment assignment).get column = assignment column := by
  rfl

private theorem query_environment_data (assignment : Nat → ZMod babyBearModulus)
    (name : String) (arity : Nat) :
    (Verification.environment assignment).data name arity = #[] := by
  rfl

/-- Phase notation for the same scalar scratch assignment. The equality
below proves every parameter from the actual loop geometry. -/
private def phasePooledAssignment (index : Fin 55) (phase : Fin 4) :
    Nat → ZMod babyBearModulus :=
  pooledAssignment (decide (phase.val = 1 ∨ phase.val = 3))
    (decide (phase.val = 3)) (decide (phase.val = 3 ∧ index.val < 54))
    (if phase.val = 3 then 54 - index.val else #v[132, 136, 148, 152][phase])
    (#v[132, 144, 148, if index.val < 54 then 128 else 152][phase])

private theorem loop_pooled_phase (variant : Variant) (index : Fin 55) (phase : Fin 4) :
    loopPooledAssignment variant index phase = phasePooledAssignment index phase := by
  have indexBound := index.isLt
  have phaseBound := phase.isLt
  have code : (rowCodeIndex (gapRow index phase)).val = 6 + phase.val :=
    congrArg Fin.val (loop_row_index index phase)
  have lower : ¬(gapRow index phase).val < 6 := by dsimp [gapRow]; omega
  have beforeFive : ¬(gapRow index phase).val < 5 := by dsimp [gapRow]; omega
  have notOne : (gapRow index phase).val ≠ 1 := by dsimp [gapRow]; omega
  have notFive : (gapRow index phase).val ≠ 5 := by dsimp [gapRow]; omega
  have upper : (gapRow index phase).val < 226 := by dsimp [gapRow]; omega
  have counter : iteration (gapRow index phase) = index.val := by dsimp [iteration, gapRow]; omega
  have remainder : ((gapRow index phase).val - 6) % 4 = phase.val := by dsimp [gapRow]; omega
  have branch : isBranch (gapRow index phase) = decide (phase.val = 3) := by
    simp only [isBranch, code, show (6 + phase.val = 9) ↔ phase.val = 3 by omega]
  have jal : isJal (gapRow index phase) = decide (phase.val = 1) := by
    simp only [isJal, code, show ¬6 + phase.val = 5 by omega, false_or,
      show (6 + phase.val = 7) ↔ phase.val = 1 by omega]
  have source : source0 variant (gapRow index phase) =
      (if phase.val = 2 then 55 - index.val else if phase.val = 3 then 54 - index.val else 0) := by
    simp only [source0, notOne, lower, upper, ↓reduceIte, remainder, counter]
  have pc : nextPC (gapRow index phase) =
      #v[132, 144, 148, if index.val < 54 then 128 else 152][phase] := by
    simp only [nextPC, beforeFive, notFive, upper, ↓reduceIte, remainder, counter]
    fin_cases phase <;> rfl
  have entry : codeEntry variant (rowCodeIndex (gapRow index phase)) =
      codeEntry variant (⟨6 + phase.val, by omega⟩ : Fin 12) :=
    congrArg (codeEntry variant) (loop_row_index index phase)
  have codePC : (codeEntry variant (rowCodeIndex (gapRow index phase))).pc.toNat =
      #v[128, 132, 144, 148][phase] := by
    rw [entry]
    fin_cases phase
    · change (128 : BitVec 32).toNat = 128
      decide +kernel
    · change (132 : BitVec 32).toNat = 132
      decide +kernel
    · change (144 : BitVec 32).toNat = 144
      decide +kernel
    · change (148 : BitVec 32).toNat = 148
      decide +kernel
  unfold loopPooledAssignment phasePooledAssignment
  simp only [branch, jal, source, codePC, pc, counter]
  fin_cases phase <;> norm_num

private theorem loop_pooled_phase_coordinate (variant : Variant) (index : Fin 55) (phase : Fin 4)
    (column : Nat) (lower : 86 ≤ column) (upper : column ≤ 127) :
    machineAssignment variant (gapRow index phase) column = phasePooledAssignment index phase column := by
  rw [loop_pooled_coordinate variant index phase column lower upper, loop_pooled_phase]

/-- Exact variable enumeration, preserving the imported expression order. -/
private def pooledVariables : Expression (ZMod babyBearModulus) → List Nat
  | .var wire => [wire.index]
  | .const _ => []
  | .add left right | .mul left right => pooledVariables left ++ pooledVariables right

private theorem pooled_expression_eval_congr (expression : Expression (ZMod babyBearModulus))
    (first second : Nat → ZMod babyBearModulus)
    (agree : ∀ column ∈ pooledVariables expression, first column = second column) :
    expression.eval (Verification.environment first) =
      expression.eval (Verification.environment second) := by
  revert agree
  induction expression with
  | var wire =>
    intro agree
    change first wire.index = second wire.index
    exact agree wire.index (by simp [pooledVariables])
  | const _ => intro _; rfl
  | add left right leftIH rightIH =>
    intro agree
    change left.eval _ + right.eval _ = left.eval _ + right.eval _
    have leftEq := leftIH (by
      intro column member
      exact agree column (by simp only [pooledVariables, List.mem_append]; exact Or.inl member))
    have rightEq := rightIH (by
      intro column member
      exact agree column (by simp only [pooledVariables, List.mem_append]; exact Or.inr member))
    rw [leftEq, rightEq]
  | mul left right leftIH rightIH =>
    intro agree
    change left.eval _ * right.eval _ = left.eval _ * right.eval _
    have leftEq := leftIH (by
      intro column member
      exact agree column (by simp only [pooledVariables, List.mem_append]; exact Or.inl member))
    have rightEq := rightIH (by
      intro column member
      exact agree column (by simp only [pooledVariables, List.mem_append]; exact Or.inr member))
    rw [leftEq, rightEq]

private theorem pooled_entry_eval_congr {arity : Nat}
    (entry : Vector (Expression (ZMod babyBearModulus)) arity)
    (first second : Nat → ZMod babyBearModulus)
    (agree : ∀ column ∈ entry.toList.flatMap pooledVariables, first column = second column) :
    entry.map (Expression.eval (Verification.environment first)) =
      entry.map (Expression.eval (Verification.environment second)) := by
  apply Vector.map_congr_left
  intro expression member
  apply pooled_expression_eval_congr
  intro column used
  exact agree column (List.mem_flatMap.mpr
    ⟨expression, Vector.mem_toList_iff.mpr member, used⟩)

/-- An exact support certificate transports the selected real lookup before
any scalar normalization. Both native environments have the same empty data. -/
private theorem queryAt_eval_congr (queries : List (Lookup (ZMod babyBearModulus)))
    (index : Nat) (first second : Nat → ZMod babyBearModulus) (columns : List Nat)
    (source : (queries[index]?.map fun query => query.entry.toList.flatMap pooledVariables) =
      some columns)
    (agree : ∀ column ∈ columns, first column = second column) :
    queryAt queries index (Verification.environment first) ↔
      queryAt queries index (Verification.environment second) := by
  cases selected : queries[index]? with
  | none => simp only [queryAt, selected]
  | some query =>
    have support : query.entry.toList.flatMap pooledVariables = columns := by
      simpa only [selected, Option.map_some, Option.some.injEq] using source
    have entries := pooled_entry_eval_congr query.entry first second (by
      intro column member
      rw [support] at member
      exact agree column member)
    simp only [queryAt, selected]
    constructor <;> intro contained
    all_goals simpa only [Lookup.Contains, query_environment_data, entries] using contained

/-- This kernel certificate inspects the actual imported query13 AST. Its
four variables are the three real query columns followed by the actual tag. -/
private theorem machine_query13_variables (variant : Variant) :
    ((gMachineQueries variant)[13]?.map fun query => query.entry.toList.flatMap pooledVariables) =
      some [89, 90, 91, 88] := by
  cases variant <;> decide +kernel

private theorem loop_pooled_13_phase_0 (variant : Variant) (index : Fin 55) :
    queryAt (gMachineQueries variant) 13
      (Verification.environment (machineAssignment variant (gapRow index 0))) := by
  have agree : ∀ column ∈ ([89, 90, 91, 88] : List Nat),
      machineAssignment variant (gapRow index 0) column = phasePooledAssignment index 0 column := by
    intro column member
    have bounded : 86 ≤ column ∧ column ≤ 127 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> decide
    exact loop_pooled_phase_coordinate variant index 0 column bounded.1 bounded.2
  apply (queryAt_eval_congr (gMachineQueries variant) 13
    (machineAssignment variant (gapRow index 0)) (phasePooledAssignment index 0)
    [89, 90, 91, 88] (machine_query13_variables variant) agree).mpr
  dsimp only [queryAt, gMachineQueries, UnifiedReduced.importedConstraints,
    FlatOperation.lookups, List.getElem?_cons_zero, List.getElem?_cons_succ]
  dsimp only [Lookup.Contains, Table.toRaw, fromElements]
  rw [query_environment_data, Array.map_empty]
  apply query_pooled_of_eq (query_unified_zero_lookup (before variant))
  apply Vector.ext
  intro column bound
  change column < 10 at bound
  interval_cases column
  all_goals norm_num [Expression.eval, query_environment_get,
    phasePooledAssignment, pooledAssignment]

/-- Exact kernel certificate for the actual imported query14 entry AST. -/
private theorem machine_query14_variables (variant : Variant) :
    ((gMachineQueries variant)[14]?.map fun query => query.entry.toList.flatMap pooledVariables) =
      some [93, 94, 95, 96, 97, 98, 99, 100, 92] := by
  cases variant <;> decide +kernel

/-- Exact kernel certificate for the actual imported query15 entry AST. -/
private theorem machine_query15_variables (variant : Variant) :
    ((gMachineQueries variant)[15]?.map fun query => query.entry.toList.flatMap pooledVariables) =
      some [102, 103, 104, 105, 106, 107, 108, 109, 101] := by
  cases variant <;> decide +kernel

/-- Exact kernel certificate for the actual imported query16 entry AST. -/
private theorem machine_query16_variables (variant : Variant) :
    ((gMachineQueries variant)[16]?.map fun query => query.entry.toList.flatMap pooledVariables) =
      some [111, 112, 113, 114, 115, 116, 117, 118, 110] := by
  cases variant <;> decide +kernel

/-- Exact kernel certificate for the actual imported query17 entry AST. -/
private theorem machine_query17_variables (variant : Variant) :
    ((gMachineQueries variant)[17]?.map fun query => query.entry.toList.flatMap pooledVariables) =
      some [120, 121, 122, 123, 124, 125, 126, 127, 119] := by
  cases variant <;> decide +kernel

private theorem loop_pooled_13_phase_1 (variant : Variant) (index : Fin 55) :
    queryAt (gMachineQueries variant) 13
      (Verification.environment (machineAssignment variant (gapRow index 1))) := by
  have agree : ∀ column ∈ ([89, 90, 91, 88] : List Nat),
      machineAssignment variant (gapRow index 1) column = phasePooledAssignment index 1 column := by
    intro column member
    have bounded : 86 ≤ column ∧ column ≤ 127 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> decide
    exact loop_pooled_phase_coordinate variant index 1 column bounded.1 bounded.2
  apply (queryAt_eval_congr (gMachineQueries variant) 13
    (machineAssignment variant (gapRow index 1)) (phasePooledAssignment index 1)
    [89, 90, 91, 88] (machine_query13_variables variant) agree).mpr
  dsimp only [queryAt, gMachineQueries, UnifiedReduced.importedConstraints,
    FlatOperation.lookups, List.getElem?_cons_zero, List.getElem?_cons_succ]
  dsimp only [Lookup.Contains, Table.toRaw, fromElements]
  rw [query_environment_data, Array.map_empty]
  apply query_pooled_of_eq (query_unified_reg_zero_lookup (before variant) 136 (by decide))
  apply Vector.ext
  intro column bound
  change column < 10 at bound
  interval_cases column
  all_goals norm_num [Expression.eval, query_environment_get, phasePooledAssignment, pooledAssignment]


private theorem loop_pooled_13_phase_2 (variant : Variant) (index : Fin 55) :
    queryAt (gMachineQueries variant) 13
      (Verification.environment (machineAssignment variant (gapRow index 2))) := by
  have agree : ∀ column ∈ ([89, 90, 91, 88] : List Nat),
      machineAssignment variant (gapRow index 2) column = phasePooledAssignment index 2 column := by
    intro column member
    have bounded : 86 ≤ column ∧ column ≤ 127 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> decide
    exact loop_pooled_phase_coordinate variant index 2 column bounded.1 bounded.2
  apply (queryAt_eval_congr (gMachineQueries variant) 13
    (machineAssignment variant (gapRow index 2)) (phasePooledAssignment index 2)
    [89, 90, 91, 88] (machine_query13_variables variant) agree).mpr
  dsimp only [queryAt, gMachineQueries, UnifiedReduced.importedConstraints,
    FlatOperation.lookups, List.getElem?_cons_zero, List.getElem?_cons_succ]
  dsimp only [Lookup.Contains, Table.toRaw, fromElements]
  rw [query_environment_data, Array.map_empty]
  apply query_pooled_of_eq (query_unified_zero_lookup (before variant))
  apply Vector.ext
  intro column bound
  change column < 10 at bound
  interval_cases column
  all_goals norm_num [Expression.eval, query_environment_get, phasePooledAssignment, pooledAssignment]


private theorem loop_pooled_13_phase_3 (variant : Variant) (index : Fin 55) :
    queryAt (gMachineQueries variant) 13
      (Verification.environment (machineAssignment variant (gapRow index 3))) := by
  have indexBound := index.isLt
  have counterZero : (54 - index.val = 0) ↔ ¬index.val < 54 := by omega
  have agree : ∀ column ∈ ([89, 90, 91, 88] : List Nat),
      machineAssignment variant (gapRow index 3) column = phasePooledAssignment index 3 column := by
    intro column member
    have bounded : 86 ≤ column ∧ column ≤ 127 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> decide
    exact loop_pooled_phase_coordinate variant index 3 column bounded.1 bounded.2
  apply (queryAt_eval_congr (gMachineQueries variant) 13
    (machineAssignment variant (gapRow index 3)) (phasePooledAssignment index 3)
    [89, 90, 91, 88] (machine_query13_variables variant) agree).mpr
  dsimp only [queryAt, gMachineQueries, UnifiedReduced.importedConstraints,
    FlatOperation.lookups, List.getElem?_cons_zero, List.getElem?_cons_succ]
  dsimp only [Lookup.Contains, Table.toRaw, fromElements]
  rw [query_environment_data, Array.map_empty]
  apply query_pooled_of_eq (query_unified_reg_zero_lookup (before variant) (54 - index.val) (by omega))
  apply Vector.ext
  intro column bound
  change column < 10 at bound
  interval_cases column
  all_goals norm_num [Expression.eval, query_environment_get, phasePooledAssignment, pooledAssignment, counterZero]


private theorem loop_pooled_14_phase_0 (variant : Variant) (index : Fin 55) :
    queryAt (gMachineQueries variant) 14
      (Verification.environment (machineAssignment variant (gapRow index 0))) := by
  have agree : ∀ column ∈ ([93, 94, 95, 96, 97, 98, 99, 100, 92] : List Nat),
      machineAssignment variant (gapRow index 0) column = phasePooledAssignment index 0 column := by
    intro column member
    have bounded : 86 ≤ column ∧ column ≤ 127 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact loop_pooled_phase_coordinate variant index 0 column bounded.1 bounded.2
  apply (queryAt_eval_congr (gMachineQueries variant) 14
    (machineAssignment variant (gapRow index 0)) (phasePooledAssignment index 0)
    [93, 94, 95, 96, 97, 98, 99, 100, 92] (machine_query14_variables variant) agree).mpr
  dsimp only [queryAt, gMachineQueries, UnifiedReduced.importedConstraints,
    FlatOperation.lookups, List.getElem?_cons_zero, List.getElem?_cons_succ]
  dsimp only [Lookup.Contains, Table.toRaw, fromElements]
  rw [query_environment_data, Array.map_empty]
  apply query_pooled_of_eq (query_unified_zero_lookup (before variant))
  apply Vector.ext
  intro column bound
  change column < 10 at bound
  interval_cases column
  all_goals norm_num [Expression.eval, query_environment_get, phasePooledAssignment, pooledAssignment]


private theorem loop_pooled_14_phase_1 (variant : Variant) (index : Fin 55) :
    queryAt (gMachineQueries variant) 14
      (Verification.environment (machineAssignment variant (gapRow index 1))) := by
  have agree : ∀ column ∈ ([93, 94, 95, 96, 97, 98, 99, 100, 92] : List Nat),
      machineAssignment variant (gapRow index 1) column = phasePooledAssignment index 1 column := by
    intro column member
    have bounded : 86 ≤ column ∧ column ≤ 127 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact loop_pooled_phase_coordinate variant index 1 column bounded.1 bounded.2
  apply (queryAt_eval_congr (gMachineQueries variant) 14
    (machineAssignment variant (gapRow index 1)) (phasePooledAssignment index 1)
    [93, 94, 95, 96, 97, 98, 99, 100, 92] (machine_query14_variables variant) agree).mpr
  dsimp only [queryAt, gMachineQueries, UnifiedReduced.importedConstraints,
    FlatOperation.lookups, List.getElem?_cons_zero, List.getElem?_cons_succ]
  dsimp only [Lookup.Contains, Table.toRaw, fromElements]
  rw [query_environment_data, Array.map_empty]
  apply query_pooled_of_eq (query_unified_positive_sign_lookup (before variant))
  apply Vector.ext
  intro column bound
  change column < 10 at bound
  interval_cases column
  all_goals norm_num [Expression.eval, query_environment_get, phasePooledAssignment, pooledAssignment]


private theorem loop_pooled_14_phase_2 (variant : Variant) (index : Fin 55) :
    queryAt (gMachineQueries variant) 14
      (Verification.environment (machineAssignment variant (gapRow index 2))) := by
  have agree : ∀ column ∈ ([93, 94, 95, 96, 97, 98, 99, 100, 92] : List Nat),
      machineAssignment variant (gapRow index 2) column = phasePooledAssignment index 2 column := by
    intro column member
    have bounded : 86 ≤ column ∧ column ≤ 127 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact loop_pooled_phase_coordinate variant index 2 column bounded.1 bounded.2
  apply (queryAt_eval_congr (gMachineQueries variant) 14
    (machineAssignment variant (gapRow index 2)) (phasePooledAssignment index 2)
    [93, 94, 95, 96, 97, 98, 99, 100, 92] (machine_query14_variables variant) agree).mpr
  dsimp only [queryAt, gMachineQueries, UnifiedReduced.importedConstraints,
    FlatOperation.lookups, List.getElem?_cons_zero, List.getElem?_cons_succ]
  dsimp only [Lookup.Contains, Table.toRaw, fromElements]
  rw [query_environment_data, Array.map_empty]
  apply query_pooled_of_eq (query_unified_zero_lookup (before variant))
  apply Vector.ext
  intro column bound
  change column < 10 at bound
  interval_cases column
  all_goals norm_num [Expression.eval, query_environment_get, phasePooledAssignment, pooledAssignment]


private theorem loop_pooled_14_phase_3 (variant : Variant) (index : Fin 55) :
    queryAt (gMachineQueries variant) 14
      (Verification.environment (machineAssignment variant (gapRow index 3))) := by
  have agree : ∀ column ∈ ([93, 94, 95, 96, 97, 98, 99, 100, 92] : List Nat),
      machineAssignment variant (gapRow index 3) column = phasePooledAssignment index 3 column := by
    intro column member
    have bounded : 86 ≤ column ∧ column ≤ 127 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact loop_pooled_phase_coordinate variant index 3 column bounded.1 bounded.2
  apply (queryAt_eval_congr (gMachineQueries variant) 14
    (machineAssignment variant (gapRow index 3)) (phasePooledAssignment index 3)
    [93, 94, 95, 96, 97, 98, 99, 100, 92] (machine_query14_variables variant) agree).mpr
  dsimp only [queryAt, gMachineQueries, UnifiedReduced.importedConstraints,
    FlatOperation.lookups, List.getElem?_cons_zero, List.getElem?_cons_succ]
  dsimp only [Lookup.Contains, Table.toRaw, fromElements]
  rw [query_environment_data, Array.map_empty]
  apply query_pooled_of_eq (query_unified_positive_sign_lookup (before variant))
  apply Vector.ext
  intro column bound
  change column < 10 at bound
  interval_cases column
  all_goals norm_num [Expression.eval, query_environment_get, phasePooledAssignment, pooledAssignment]


private theorem loop_pooled_15_phase_0 (variant : Variant) (index : Fin 55) :
    queryAt (gMachineQueries variant) 15
      (Verification.environment (machineAssignment variant (gapRow index 0))) := by
  have agree : ∀ column ∈ ([102, 103, 104, 105, 106, 107, 108, 109, 101] : List Nat),
      machineAssignment variant (gapRow index 0) column = phasePooledAssignment index 0 column := by
    intro column member
    have bounded : 86 ≤ column ∧ column ≤ 127 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact loop_pooled_phase_coordinate variant index 0 column bounded.1 bounded.2
  apply (queryAt_eval_congr (gMachineQueries variant) 15
    (machineAssignment variant (gapRow index 0)) (phasePooledAssignment index 0)
    [102, 103, 104, 105, 106, 107, 108, 109, 101] (machine_query15_variables variant) agree).mpr
  dsimp only [queryAt, gMachineQueries, UnifiedReduced.importedConstraints,
    FlatOperation.lookups, List.getElem?_cons_zero, List.getElem?_cons_succ]
  dsimp only [Lookup.Contains, Table.toRaw, fromElements]
  rw [query_environment_data, Array.map_empty]
  apply query_pooled_of_eq (query_unified_zero_lookup (before variant))
  apply Vector.ext
  intro column bound
  change column < 10 at bound
  interval_cases column
  all_goals norm_num [Expression.eval, query_environment_get, phasePooledAssignment, pooledAssignment]


private theorem loop_pooled_15_phase_1 (variant : Variant) (index : Fin 55) :
    queryAt (gMachineQueries variant) 15
      (Verification.environment (machineAssignment variant (gapRow index 1))) := by
  have agree : ∀ column ∈ ([102, 103, 104, 105, 106, 107, 108, 109, 101] : List Nat),
      machineAssignment variant (gapRow index 1) column = phasePooledAssignment index 1 column := by
    intro column member
    have bounded : 86 ≤ column ∧ column ≤ 127 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact loop_pooled_phase_coordinate variant index 1 column bounded.1 bounded.2
  apply (queryAt_eval_congr (gMachineQueries variant) 15
    (machineAssignment variant (gapRow index 1)) (phasePooledAssignment index 1)
    [102, 103, 104, 105, 106, 107, 108, 109, 101] (machine_query15_variables variant) agree).mpr
  dsimp only [queryAt, gMachineQueries, UnifiedReduced.importedConstraints,
    FlatOperation.lookups, List.getElem?_cons_zero, List.getElem?_cons_succ]
  dsimp only [Lookup.Contains, Table.toRaw, fromElements]
  rw [query_environment_data, Array.map_empty]
  apply query_pooled_of_eq (query_unified_positive_sign_lookup (before variant))
  apply Vector.ext
  intro column bound
  change column < 10 at bound
  interval_cases column
  all_goals norm_num [Expression.eval, query_environment_get, phasePooledAssignment, pooledAssignment]


private theorem loop_pooled_15_phase_2 (variant : Variant) (index : Fin 55) :
    queryAt (gMachineQueries variant) 15
      (Verification.environment (machineAssignment variant (gapRow index 2))) := by
  have agree : ∀ column ∈ ([102, 103, 104, 105, 106, 107, 108, 109, 101] : List Nat),
      machineAssignment variant (gapRow index 2) column = phasePooledAssignment index 2 column := by
    intro column member
    have bounded : 86 ≤ column ∧ column ≤ 127 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact loop_pooled_phase_coordinate variant index 2 column bounded.1 bounded.2
  apply (queryAt_eval_congr (gMachineQueries variant) 15
    (machineAssignment variant (gapRow index 2)) (phasePooledAssignment index 2)
    [102, 103, 104, 105, 106, 107, 108, 109, 101] (machine_query15_variables variant) agree).mpr
  dsimp only [queryAt, gMachineQueries, UnifiedReduced.importedConstraints,
    FlatOperation.lookups, List.getElem?_cons_zero, List.getElem?_cons_succ]
  dsimp only [Lookup.Contains, Table.toRaw, fromElements]
  rw [query_environment_data, Array.map_empty]
  apply query_pooled_of_eq (query_unified_zero_lookup (before variant))
  apply Vector.ext
  intro column bound
  change column < 10 at bound
  interval_cases column
  all_goals norm_num [Expression.eval, query_environment_get, phasePooledAssignment, pooledAssignment]


private theorem loop_pooled_15_phase_3 (variant : Variant) (index : Fin 55) :
    queryAt (gMachineQueries variant) 15
      (Verification.environment (machineAssignment variant (gapRow index 3))) := by
  have agree : ∀ column ∈ ([102, 103, 104, 105, 106, 107, 108, 109, 101] : List Nat),
      machineAssignment variant (gapRow index 3) column = phasePooledAssignment index 3 column := by
    intro column member
    have bounded : 86 ≤ column ∧ column ≤ 127 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact loop_pooled_phase_coordinate variant index 3 column bounded.1 bounded.2
  apply (queryAt_eval_congr (gMachineQueries variant) 15
    (machineAssignment variant (gapRow index 3)) (phasePooledAssignment index 3)
    [102, 103, 104, 105, 106, 107, 108, 109, 101] (machine_query15_variables variant) agree).mpr
  dsimp only [queryAt, gMachineQueries, UnifiedReduced.importedConstraints,
    FlatOperation.lookups, List.getElem?_cons_zero, List.getElem?_cons_succ]
  dsimp only [Lookup.Contains, Table.toRaw, fromElements]
  rw [query_environment_data, Array.map_empty]
  apply query_pooled_of_eq (query_unified_positive_sign_lookup (before variant))
  apply Vector.ext
  intro column bound
  change column < 10 at bound
  interval_cases column
  all_goals norm_num [Expression.eval, query_environment_get, phasePooledAssignment, pooledAssignment]


private theorem loop_pooled_16_phase_0 (variant : Variant) (index : Fin 55) :
    queryAt (gMachineQueries variant) 16
      (Verification.environment (machineAssignment variant (gapRow index 0))) := by
  have agree : ∀ column ∈ ([111, 112, 113, 114, 115, 116, 117, 118, 110] : List Nat),
      machineAssignment variant (gapRow index 0) column = phasePooledAssignment index 0 column := by
    intro column member
    have bounded : 86 ≤ column ∧ column ≤ 127 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact loop_pooled_phase_coordinate variant index 0 column bounded.1 bounded.2
  apply (queryAt_eval_congr (gMachineQueries variant) 16
    (machineAssignment variant (gapRow index 0)) (phasePooledAssignment index 0)
    [111, 112, 113, 114, 115, 116, 117, 118, 110] (machine_query16_variables variant) agree).mpr
  dsimp only [queryAt, gMachineQueries, UnifiedReduced.importedConstraints,
    FlatOperation.lookups, List.getElem?_cons_zero, List.getElem?_cons_succ]
  dsimp only [Lookup.Contains, Table.toRaw, fromElements]
  rw [query_environment_data, Array.map_empty]
  apply query_pooled_of_eq (query_unified_zero_lookup (before variant))
  apply Vector.ext
  intro column bound
  change column < 10 at bound
  interval_cases column
  all_goals norm_num [Expression.eval, query_environment_get, phasePooledAssignment, pooledAssignment]


private theorem loop_pooled_16_phase_1 (variant : Variant) (index : Fin 55) :
    queryAt (gMachineQueries variant) 16
      (Verification.environment (machineAssignment variant (gapRow index 1))) := by
  have agree : ∀ column ∈ ([111, 112, 113, 114, 115, 116, 117, 118, 110] : List Nat),
      machineAssignment variant (gapRow index 1) column = phasePooledAssignment index 1 column := by
    intro column member
    have bounded : 86 ≤ column ∧ column ≤ 127 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact loop_pooled_phase_coordinate variant index 1 column bounded.1 bounded.2
  apply (queryAt_eval_congr (gMachineQueries variant) 16
    (machineAssignment variant (gapRow index 1)) (phasePooledAssignment index 1)
    [111, 112, 113, 114, 115, 116, 117, 118, 110] (machine_query16_variables variant) agree).mpr
  dsimp only [queryAt, gMachineQueries, UnifiedReduced.importedConstraints,
    FlatOperation.lookups, List.getElem?_cons_zero, List.getElem?_cons_succ]
  dsimp only [Lookup.Contains, Table.toRaw, fromElements]
  rw [query_environment_data, Array.map_empty]
  apply query_pooled_of_eq (query_unified_conditional_lookup (before variant) 0)
  apply Vector.ext
  intro column bound
  change column < 10 at bound
  interval_cases column
  all_goals norm_num [Expression.eval, query_environment_get, phasePooledAssignment, pooledAssignment]


private theorem loop_pooled_16_phase_2 (variant : Variant) (index : Fin 55) :
    queryAt (gMachineQueries variant) 16
      (Verification.environment (machineAssignment variant (gapRow index 2))) := by
  have agree : ∀ column ∈ ([111, 112, 113, 114, 115, 116, 117, 118, 110] : List Nat),
      machineAssignment variant (gapRow index 2) column = phasePooledAssignment index 2 column := by
    intro column member
    have bounded : 86 ≤ column ∧ column ≤ 127 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact loop_pooled_phase_coordinate variant index 2 column bounded.1 bounded.2
  apply (queryAt_eval_congr (gMachineQueries variant) 16
    (machineAssignment variant (gapRow index 2)) (phasePooledAssignment index 2)
    [111, 112, 113, 114, 115, 116, 117, 118, 110] (machine_query16_variables variant) agree).mpr
  dsimp only [queryAt, gMachineQueries, UnifiedReduced.importedConstraints,
    FlatOperation.lookups, List.getElem?_cons_zero, List.getElem?_cons_succ]
  dsimp only [Lookup.Contains, Table.toRaw, fromElements]
  rw [query_environment_data, Array.map_empty]
  apply query_pooled_of_eq (query_unified_zero_lookup (before variant))
  apply Vector.ext
  intro column bound
  change column < 10 at bound
  interval_cases column
  all_goals norm_num [Expression.eval, query_environment_get, phasePooledAssignment, pooledAssignment]


private theorem loop_pooled_16_phase_3 (variant : Variant) (index : Fin 55) :
    queryAt (gMachineQueries variant) 16
      (Verification.environment (machineAssignment variant (gapRow index 3))) := by
  have agree : ∀ column ∈ ([111, 112, 113, 114, 115, 116, 117, 118, 110] : List Nat),
      machineAssignment variant (gapRow index 3) column = phasePooledAssignment index 3 column := by
    intro column member
    have bounded : 86 ≤ column ∧ column ≤ 127 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact loop_pooled_phase_coordinate variant index 3 column bounded.1 bounded.2
  apply (queryAt_eval_congr (gMachineQueries variant) 16
    (machineAssignment variant (gapRow index 3)) (phasePooledAssignment index 3)
    [111, 112, 113, 114, 115, 116, 117, 118, 110] (machine_query16_variables variant) agree).mpr
  dsimp only [queryAt, gMachineQueries, UnifiedReduced.importedConstraints,
    FlatOperation.lookups, List.getElem?_cons_zero, List.getElem?_cons_succ]
  dsimp only [Lookup.Contains, Table.toRaw, fromElements]
  rw [query_environment_data, Array.map_empty]
  by_cases branchTaken : index.val < 54
  · apply query_pooled_of_eq (query_unified_conditional_lookup (before variant) 1)
    apply Vector.ext
    intro column bound
    change column < 10 at bound
    interval_cases column
    all_goals norm_num [Expression.eval, query_environment_get, phasePooledAssignment, pooledAssignment, branchTaken]
  · apply query_pooled_of_eq (query_unified_conditional_lookup (before variant) 2)
    apply Vector.ext
    intro column bound
    change column < 10 at bound
    interval_cases column
    all_goals norm_num [Expression.eval, query_environment_get, phasePooledAssignment, pooledAssignment, branchTaken]


private theorem loop_pooled_17_phase_0 (variant : Variant) (index : Fin 55) :
    queryAt (gMachineQueries variant) 17
      (Verification.environment (machineAssignment variant (gapRow index 0))) := by
  have agree : ∀ column ∈ ([120, 121, 122, 123, 124, 125, 126, 127, 119] : List Nat),
      machineAssignment variant (gapRow index 0) column = phasePooledAssignment index 0 column := by
    intro column member
    have bounded : 86 ≤ column ∧ column ≤ 127 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact loop_pooled_phase_coordinate variant index 0 column bounded.1 bounded.2
  apply (queryAt_eval_congr (gMachineQueries variant) 17
    (machineAssignment variant (gapRow index 0)) (phasePooledAssignment index 0)
    [120, 121, 122, 123, 124, 125, 126, 127, 119] (machine_query17_variables variant) agree).mpr
  dsimp only [queryAt, gMachineQueries, UnifiedReduced.importedConstraints,
    FlatOperation.lookups, List.getElem?_cons_zero, List.getElem?_cons_succ]
  dsimp only [Lookup.Contains, Table.toRaw, fromElements]
  rw [query_environment_data, Array.map_empty]
  apply query_pooled_of_eq (query_unified_zero_lookup (before variant))
  apply Vector.ext
  intro column bound
  change column < 10 at bound
  interval_cases column
  all_goals norm_num [Expression.eval, query_environment_get, phasePooledAssignment, pooledAssignment]


private theorem loop_pooled_17_phase_1 (variant : Variant) (index : Fin 55) :
    queryAt (gMachineQueries variant) 17
      (Verification.environment (machineAssignment variant (gapRow index 1))) := by
  have agree : ∀ column ∈ ([120, 121, 122, 123, 124, 125, 126, 127, 119] : List Nat),
      machineAssignment variant (gapRow index 1) column = phasePooledAssignment index 1 column := by
    intro column member
    have bounded : 86 ≤ column ∧ column ≤ 127 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact loop_pooled_phase_coordinate variant index 1 column bounded.1 bounded.2
  apply (queryAt_eval_congr (gMachineQueries variant) 17
    (machineAssignment variant (gapRow index 1)) (phasePooledAssignment index 1)
    [120, 121, 122, 123, 124, 125, 126, 127, 119] (machine_query17_variables variant) agree).mpr
  dsimp only [queryAt, gMachineQueries, UnifiedReduced.importedConstraints,
    FlatOperation.lookups, List.getElem?_cons_zero, List.getElem?_cons_succ]
  dsimp only [Lookup.Contains, Table.toRaw, fromElements]
  rw [query_environment_data, Array.map_empty]
  apply query_pooled_of_eq (query_unified_cleanup_lookup (before variant) 144 (by decide) (by decide))
  apply Vector.ext
  intro column bound
  change column < 10 at bound
  interval_cases column
  all_goals norm_num [Expression.eval, query_environment_get, phasePooledAssignment, pooledAssignment]


private theorem loop_pooled_17_phase_2 (variant : Variant) (index : Fin 55) :
    queryAt (gMachineQueries variant) 17
      (Verification.environment (machineAssignment variant (gapRow index 2))) := by
  have agree : ∀ column ∈ ([120, 121, 122, 123, 124, 125, 126, 127, 119] : List Nat),
      machineAssignment variant (gapRow index 2) column = phasePooledAssignment index 2 column := by
    intro column member
    have bounded : 86 ≤ column ∧ column ≤ 127 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact loop_pooled_phase_coordinate variant index 2 column bounded.1 bounded.2
  apply (queryAt_eval_congr (gMachineQueries variant) 17
    (machineAssignment variant (gapRow index 2)) (phasePooledAssignment index 2)
    [120, 121, 122, 123, 124, 125, 126, 127, 119] (machine_query17_variables variant) agree).mpr
  dsimp only [queryAt, gMachineQueries, UnifiedReduced.importedConstraints,
    FlatOperation.lookups, List.getElem?_cons_zero, List.getElem?_cons_succ]
  dsimp only [Lookup.Contains, Table.toRaw, fromElements]
  rw [query_environment_data, Array.map_empty]
  apply query_pooled_of_eq (query_unified_zero_lookup (before variant))
  apply Vector.ext
  intro column bound
  change column < 10 at bound
  interval_cases column
  all_goals norm_num [Expression.eval, query_environment_get, phasePooledAssignment, pooledAssignment]


private theorem loop_pooled_17_phase_3 (variant : Variant) (index : Fin 55) :
    queryAt (gMachineQueries variant) 17
      (Verification.environment (machineAssignment variant (gapRow index 3))) := by
  have agree : ∀ column ∈ ([120, 121, 122, 123, 124, 125, 126, 127, 119] : List Nat),
      machineAssignment variant (gapRow index 3) column = phasePooledAssignment index 3 column := by
    intro column member
    have bounded : 86 ≤ column ∧ column ≤ 127 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact loop_pooled_phase_coordinate variant index 3 column bounded.1 bounded.2
  apply (queryAt_eval_congr (gMachineQueries variant) 17
    (machineAssignment variant (gapRow index 3)) (phasePooledAssignment index 3)
    [120, 121, 122, 123, 124, 125, 126, 127, 119] (machine_query17_variables variant) agree).mpr
  dsimp only [queryAt, gMachineQueries, UnifiedReduced.importedConstraints,
    FlatOperation.lookups, List.getElem?_cons_zero, List.getElem?_cons_succ]
  dsimp only [Lookup.Contains, Table.toRaw, fromElements]
  rw [query_environment_data, Array.map_empty]
  by_cases branchTaken : index.val < 54
  · apply query_pooled_of_eq (query_unified_cleanup_lookup (before variant) 128 (by decide) (by decide))
    apply Vector.ext
    intro column bound
    change column < 10 at bound
    interval_cases column
    all_goals norm_num [Expression.eval, query_environment_get, phasePooledAssignment, pooledAssignment, branchTaken]
  · apply query_pooled_of_eq (query_unified_cleanup_lookup (before variant) 152 (by decide) (by decide))
    apply Vector.ext
    intro column bound
    change column < 10 at bound
    interval_cases column
    all_goals norm_num [Expression.eval, query_environment_get, phasePooledAssignment, pooledAssignment, branchTaken]


private theorem loop_machine_pooled_query (variant : Variant) (index : Fin 55) (phase : Fin 4)
    (slot : Nat) (slotLower : 13 ≤ slot) (slotBound : slot < 18) :
    queryAt (gMachineQueries variant) slot
      (Verification.environment (machineAssignment variant (gapRow index phase))) := by
  interval_cases slot <;> fin_cases phase
  · exact loop_pooled_13_phase_0 variant index
  · exact loop_pooled_13_phase_1 variant index
  · exact loop_pooled_13_phase_2 variant index
  · exact loop_pooled_13_phase_3 variant index
  · exact loop_pooled_14_phase_0 variant index
  · exact loop_pooled_14_phase_1 variant index
  · exact loop_pooled_14_phase_2 variant index
  · exact loop_pooled_14_phase_3 variant index
  · exact loop_pooled_15_phase_0 variant index
  · exact loop_pooled_15_phase_1 variant index
  · exact loop_pooled_15_phase_2 variant index
  · exact loop_pooled_15_phase_3 variant index
  · exact loop_pooled_16_phase_0 variant index
  · exact loop_pooled_16_phase_1 variant index
  · exact loop_pooled_16_phase_2 variant index
  · exact loop_pooled_16_phase_3 variant index
  · exact loop_pooled_17_phase_0 variant index
  · exact loop_pooled_17_phase_1 variant index
  · exact loop_pooled_17_phase_2 variant index
  · exact loop_pooled_17_phase_3 variant index

private theorem loop_machine_query (variant : Variant) (index : Fin 55) (phase : Fin 4)
    (slot : Nat) (slotBound : slot < 18) :
    queryAt (gMachineQueries variant) slot
      (Verification.environment (machineAssignment variant (gapRow index phase))) := by
  by_cases range : slot < 13
  · exact machine_ranges_of_bounds variant _ (loop_range_bounded variant index phase) slot range
  · exact loop_machine_pooled_query variant index phase slot (by omega) slotBound

private theorem final_machine_query (variant : Variant) (last : Fin 2) (slot : Nat) (slotBound : slot < 18) :
    queryAt (gMachineQueries variant) slot
        (Verification.environment
          (machineAssignment variant ⟨226 + last.val, by have := last.isLt; omega⟩)) := by
  by_cases range : slot < 13
  · interval_cases slot
    all_goals dsimp only [queryAt, gMachineQueries, UnifiedReduced.importedConstraints,
      FlatOperation.lookups, List.getElem?_cons_zero, List.getElem?_cons_succ]
    all_goals apply Verification.range16_contains
    all_goals fin_cases last <;> cases variant <;> decide +kernel
  · have pooled : 13 ≤ slot := by omega
    interval_cases slot
    all_goals dsimp only [queryAt, gMachineQueries, UnifiedReduced.importedConstraints,
      FlatOperation.lookups, List.getElem?_cons_zero, List.getElem?_cons_succ]
    all_goals dsimp only [Lookup.Contains, Table.toRaw, Verification.environment, fromElements]
    all_goals rw [Array.map_empty]
    all_goals change (UnifiedReduced.Setup.table (before variant)).Contains #[] _
    all_goals apply query_pooled_of_eq (query_unified_zero_lookup (before variant))
    all_goals fin_cases last <;> cases variant <;> decide +kernel

/-- The complete actual228-row CPU modeled-query obligation. -/
theorem machine_queries (variant : Variant) (index : Fin 228) :
    ∀ lookup ∈ FlatOperation.lookups
      (UnifiedReduced.importedConstraints (data variant).machine.rom),
      lookup.Contains (Verification.environment (machineAssignment variant index)) := by
  rw [List.forall_mem_iff_forall_getElem]
  intro query bound
  change query < (gMachineQueries variant).length at bound
  have short : query < 18 := by simpa only [g_machine_query_count] using bound
  change Lookup.Contains ((gMachineQueries variant)[query]'bound)
    (Verification.environment (machineAssignment variant index))
  apply queryAt_getElem _ _ _ bound
  by_cases early : index.val < 6
  · exact boot_machine_query variant ⟨index.val, early⟩ query short
  · by_cases loop : index.val < 226
    · let iterationIndex : Fin 55 := ⟨(index.val - 6) / 4, by omega⟩
      let phase : Fin 4 := ⟨(index.val - 6) % 4, Nat.mod_lt _ (by decide)⟩
      have same : index = gapRow iterationIndex phase := by
        apply Fin.ext
        dsimp [gapRow, iterationIndex, phase]
        omega
      rw [same]
      exact loop_machine_query variant iterationIndex phase query short
    · let last : Fin 2 := ⟨index.val - 226, by have := index.isLt; omega⟩
      have same : index = (⟨226 + last.val, by have := last.isLt; omega⟩ : Fin 228) := by
        apply Fin.ext
        dsimp [last]
        omega
      rw [same]
      exact final_machine_query variant last query short

private theorem query_timestamp_nat (value : Nat) (bound : value < timestampBase) :
    (value : ZMod babyBearModulus).val < timestampBase := by
  have canonical : value < babyBearModulus := by
    dsimp [timestampBase, babyBearModulus] at *
    omega
  rw [ZMod.val_natCast_of_lt canonical]
  exact bound

private theorem query_borrowed_low (current previous : Nat)
    (past : previous < current) (small : current < 916) :
    ((previous : ZMod babyBearModulus) - current + timestampBase).val < timestampBase := by
  have subtraction : current ≤ timestampBase + previous := by
    dsimp [timestampBase]
    omega
  have canonical : timestampBase + previous - current < babyBearModulus := by
    dsimp [timestampBase, babyBearModulus]
    omega
  have bounded : timestampBase + previous - current < timestampBase := by omega
  have fieldIdentity : ((timestampBase + previous - current : Nat) : ZMod babyBearModulus) =
      (previous : ZMod babyBearModulus) - current + timestampBase := by
    rw [Nat.cast_sub subtraction]
    push_cast
    ring
  rw [← fieldIdentity, ZMod.val_natCast_of_lt canonical]
  exact bounded

/-- All eight imported queries over abstract coordinates. The three prior
values stay opaque while the field expressions and their ranges are proved. -/
private theorem machine_timestamps_of_coordinates
    (assignment : Nat → ZMod babyBearModulus) (current : Nat) (prior : Fin 3 → Nat)
    (finalBound : current + 4 < timestampBase)
    (past : ∀ port : Fin 3, prior port < current + port.val)
    (small : ∀ port : Fin 3, current + port.val < 916)
    (c2 : assignment 2 = current) (c3 : assignment 3 = 0)
    (c32 : assignment 32 = (current : ZMod babyBearModulus) + 4)
    (c33 : assignment 33 = 0)
    (c34 : assignment 34 = prior 0) (c35 : assignment 35 = 0)
    (c40 : assignment 40 = prior 1) (c41 : assignment 41 = 0)
    (c46 : assignment 46 = prior 2) (c47 : assignment 47 = 0)
    (c131 : assignment 131 = 1) (c132 : assignment 132 = 1)
    (c133 : assignment 133 = 1) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment assignment)
      UnifiedReduced.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro query bound
    have short : query < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
    apply queryAt_getElem _ _ _ bound
    interval_cases query
    all_goals dsimp only [queryAt, UnifiedReduced.importedConstraintsTimestampLookups,
      FlatOperation.lookups, List.getElem?_cons_zero, List.getElem?_cons_succ]
    all_goals apply Trace.Proofs.range_contains
    · simpa [Expression.eval, query_environment_get, c32, Nat.cast_add]
        using query_timestamp_nat (current + 4) finalBound
    · norm_num [Expression.eval, query_environment_get, c33,
        timestampBase, babyBearModulus]
    · have low := query_borrowed_low (current + (0 : Fin 3).val) (prior 0)
        (past 0) (small 0)
      simpa [Expression.eval, query_environment_get, c2, c34, c131, Nat.cast_add,
        sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using low
    · norm_num [Expression.eval, query_environment_get, c3, c35, c131,
        timestampBase, babyBearModulus]
      exact query_timestamp_nat 524287 (by decide)
    · have low := query_borrowed_low (current + (1 : Fin 3).val) (prior 1)
        (past 1) (small 1)
      simpa [Expression.eval, query_environment_get, c2, c40, c132, Nat.cast_add,
        sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using low
    · norm_num [Expression.eval, query_environment_get, c3, c41, c132,
        timestampBase, babyBearModulus]
      exact query_timestamp_nat 524287 (by decide)
    · have low := query_borrowed_low (current + (2 : Fin 3).val) (prior 2)
        (past 2) (small 2)
      simpa [Expression.eval, query_environment_get, c2, c46, c133, Nat.cast_add,
        sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using low
    · norm_num [Expression.eval, query_environment_get, c3, c47, c133,
        timestampBase, babyBearModulus]
      exact query_timestamp_nat 524287 (by decide)

/-- Every actual CPU timestamp query follows from the native coordinates and
proved chronological bounds. No history is normalized beneath a field value. -/
theorem machine_timestamps (variant : Variant) (index : Fin 228) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (machineAssignment variant index))
      UnifiedReduced.importedConstraintsTimestampLookups := by
  apply machine_timestamps_of_coordinates (machineAssignment variant index)
    (machineClock index) (previous variant index)
  · have rowBound := index.isLt
    dsimp [machineClock, timestampBase]
    omega
  · exact cpu_previous_before_current variant index
  · exact current_cpu_clock_bound index
  all_goals rfl

/-- All21 original worker core queries are proved on a coordinate projection,
then transported back through exact imported-AST support. The chronological
worker timestamps remain in the actual witness and their separate obligations. -/
private theorem g_query_row (query : Vector (ZMod babyBearModulus) 9) (index : Fin 344896)
    (same : query = (Blake2G.referenceSetupRow Blake2G.Control.controllerRows index).map
      (fun value : Nat => (value : ZMod babyBearModulus))) :
    (Blake2G.setupTable Blake2G.Control.controllerRows).Contains #[] query := by
  change ∃ row : Fin 344896, query = (Blake2G.setupRow Blake2G.Control.controllerRows row).map
    (fun value : Nat => (value : ZMod babyBearModulus))
  refine ⟨index, ?_⟩
  rw [Blake2G.Proofs.setup_row_characterization]
  exact same

private theorem g_query_zero_lookup (kind : Fin 5) :
    (Blake2G.setupTable Blake2G.Control.controllerRows (p := babyBearModulus)).Contains #[]
      #v[0, 0, 0, 0, 0, 0, 0, 0, (#v[4, 17, 18, 19, 20][kind] : Nat)] := by
  have zeroRow : Blake2G.referenceSetupRow Blake2G.Control.controllerRows
      ⟨(#v[0, 65536, 65600, 65856, 82240][kind] : Nat), by fin_cases kind <;> decide⟩ =
      #v[0, 0, 0, 0, 0, 0, 0, 0, (#v[4, 17, 18, 19, 20][kind] : Nat)] := by
    fin_cases kind <;> norm_num [Blake2G.referenceSetupRow, Blake2G.xorRow]
  apply g_query_row _
    ⟨(#v[0, 65536, 65600, 65856, 82240][kind] : Nat), by fin_cases kind <;> decide⟩
  rw [zeroRow]
  ext column bound
  interval_cases column <;> simp

/-- A small Nat constructor keeps the abstract controller vector opaque until
its existing exact row theorem has been applied. -/
private def g_query_controller_nat (key : Fin 512) (outputs : Vector Nat 7) : Vector Nat 9 :=
  #v[key.val, outputs[0], outputs[1], outputs[2], outputs[3], outputs[4], outputs[5], outputs[6], 28]

private theorem g_query_controller_reference (control : Fin 512 → Vector Nat 7) (key : Fin 512) :
    Blake2G.referenceSetupRow control ⟨344384 + key.val, by have := key.isLt; omega⟩ =
      g_query_controller_nat key (control key) := by
  have small := key.isLt
  have difference : 344384 + key.val - 344384 = key.val := by omega
  have selected : (⟨344384 + key.val - 344384, by omega⟩ : Fin 512) = key := by
    apply Fin.ext
    change 344384 + key.val - 344384 = key.val
    exact difference
  simp only [Blake2G.referenceSetupRow,
    show ¬344384 + key.val < 65536 by omega,
    show ¬344384 + key.val < 65600 by omega,
    show ¬344384 + key.val < 65856 by omega,
    show ¬344384 + key.val < 82240 by omega,
    show ¬344384 + key.val < 344384 by omega, ↓reduceDIte, ↓reduceIte]
  let chosen : Fin 512 := ⟨344384 + key.val - 344384, by omega⟩
  change g_query_controller_nat chosen (control chosen) =
    g_query_controller_nat key (control key)
  exact congrArg (fun chosen : Fin 512 => g_query_controller_nat chosen (control chosen)) selected

private theorem g_query_controller_output (key : Fin 512) (output : Blake2G.Control.Output) :
    g_query_controller_nat key output.row =
      #v[key.val, output.register.lo,
        output.stateOffsets[0], output.stateOffsets[1], output.stateOffsets[2], output.stateOffsets[3],
        output.messageOffsets[0], output.messageOffsets[1], 28] := by
  ext column bound
  interval_cases column <;> simp [g_query_controller_nat, Blake2G.Control.Output.row]

private theorem g_query_controller_lookup (input : Blake2G.Control.Input) :
    (Blake2G.setupTable Blake2G.Control.controllerRows (p := babyBearModulus)).Contains #[]
      #v[input.key.val, (Blake2G.Control.step input).register.lo,
        (Blake2G.Control.step input).stateOffsets[0], (Blake2G.Control.step input).stateOffsets[1],
        (Blake2G.Control.step input).stateOffsets[2], (Blake2G.Control.step input).stateOffsets[3],
        (Blake2G.Control.step input).messageOffsets[0], (Blake2G.Control.step input).messageOffsets[1], 28] := by
  have reference := g_query_controller_reference Blake2G.Control.controllerRows input.key
  have controller := congrArg (g_query_controller_nat input.key)
    (Blake2G.Control.Proofs.controller_input input)
  have row := reference.trans (controller.trans (g_query_controller_output input.key (Blake2G.Control.step input)))
  apply g_query_row _ ⟨344384 + input.key.val, by have := input.key.isLt; omega⟩
  rw [row]
  ext column bound
  interval_cases column <;> simp

private theorem g_query_of_eq {query expected : Vector (ZMod babyBearModulus) 9}
    (member : (Blake2G.setupTable Blake2G.Control.controllerRows).Contains #[] expected)
    (same : query = expected) :
    (Blake2G.setupTable Blake2G.Control.controllerRows).Contains #[] query := by
  rw [same]
  exact member

/-- Freeze only the type of the actual filtered lookup list, not its values. -/
private def gWorkerCoreQueries : List (Lookup (ZMod babyBearModulus)) :=
  FlatOperation.lookups (Blake2G.importedConstraints
    (Blake2G.setupTable Blake2G.Control.controllerRows))

private theorem g_worker_core_query_count : gWorkerCoreQueries.length = 21 := by rfl

/-- Native non-timestamp coordinates, copied without the chronological
workerReadStamp branch. Variant affects only that removed branch. -/
private def gWorkerCoreAssignment (index : Fin 56) (column : Nat) : ZMod babyBearModulus :=
  let control := Blake2G.Control.step (Blake2G.controllerAt true index.val)
  if column = 0 then 1
  else if column = 1 then callStart index + 1
  else if column = 3 then (Blake2G.controlAt true index.val).lo
  else if column = 5 then control.register.lo
  else if stateOffset : 7 ≤ column ∧ column < 11 then control.stateOffsets[column - 7]'(by omega)
  else if messageOffset : 11 ≤ column ∧ column < 13 then control.messageOffsets[column - 11]'(by omega)
  else if column = 14 ∨ column = 32 then 512
  else if column = 31 then 64
  else if column = 83 then 31457280
  else 0

/-- Exact equality for every coordinate outside the actual timestamp block;
no witness value or assignment equality is assumed at an actual use. -/
private theorem g_worker_core_coordinate (variant : Variant) (index : Fin 56)
    (column : Nat) (notTimestamp : ¬ (84 ≤ column ∧ column < 111)) :
    workerAssignment variant index column = gWorkerCoreAssignment index column := by
  simp only [workerAssignment, gWorkerCoreAssignment, notTimestamp, ↓reduceDIte]

/-- Inspect all21 actual imported lookup entry ASTs. This certificate includes
both alignments, the controller and all18 XOR queries; table IDs and entry
order stay in the original lookup objects, with no query replacement. -/
private theorem g_worker_core_variables_below_timestamp :
    gWorkerCoreQueries.all (fun lookup =>
      (lookup.entry.toList.flatMap pooledVariables).all fun column => decide (column < 83)) = true := by
  decide +kernel

/-- The existing generic expression/entry congruence transports the selected
original lookup and its original table/data unchanged. Only coordinates that
actually occur in its exact AST are compared. -/
private theorem g_worker_core_query_eval_congr (variant : Variant) (index : Fin 56)
    (query : Fin 21) :
    queryAt gWorkerCoreQueries query.val (Verification.environment (workerAssignment variant index)) ↔
      queryAt gWorkerCoreQueries query.val (Verification.environment (gWorkerCoreAssignment index)) := by
  have bound : query.val < gWorkerCoreQueries.length := by
    rw [g_worker_core_query_count]
    exact query.isLt
  let lookup := gWorkerCoreQueries[query.val]'bound
  have source : (gWorkerCoreQueries[query.val]?.map fun item =>
      item.entry.toList.flatMap pooledVariables) = some (lookup.entry.toList.flatMap pooledVariables) := by
    rw [List.getElem?_eq_getElem bound]
    rfl
  have used := List.all_eq_true.mp g_worker_core_variables_below_timestamp lookup (List.getElem_mem bound)
  apply queryAt_eval_congr gWorkerCoreQueries query.val
    (workerAssignment variant index) (gWorkerCoreAssignment index)
    (lookup.entry.toList.flatMap pooledVariables) source
  intro column member
  have short : column < 83 := of_decide_eq_true (List.all_eq_true.mp used column member)
  exact g_worker_core_coordinate variant index column (by omega)

/-- Existing controller/XOR/alignment membership proofs can target the thin
coordinates, then transport back before the public actual-native conclusion. -/
private theorem g_worker_core_query_of_thin (variant : Variant) (index : Fin 56)
    (query : Fin 21)
    (checked : queryAt gWorkerCoreQueries query.val
      (Verification.environment (gWorkerCoreAssignment index))) :
    queryAt gWorkerCoreQueries query.val
      (Verification.environment (workerAssignment variant index)) :=
  (g_worker_core_query_eval_congr variant index query).mpr checked

/-- The actual emitted alignment coefficient is inverse64 in BabyBear. -/
private theorem g_query_inverse64 : (-31457280 : ZMod babyBearModulus) * 64 = 1 := by
  decide +kernel

private theorem g_worker_alignment_query (variant : Variant) (index : Fin 56) (slot : Fin 2) :
    queryAt gWorkerCoreQueries slot.val
        (Verification.environment (workerAssignment variant index)) := by
  apply g_worker_core_query_of_thin variant index
    ⟨slot.val, by have := slot.isLt; omega⟩
  fin_cases slot
  all_goals dsimp only [queryAt, gWorkerCoreQueries, Blake2G.importedConstraints,
    FlatOperation.lookups, List.getElem?_cons_zero, List.getElem?_cons_succ]
  all_goals apply Trace.Proofs.range_contains
  · simp [Expression.eval, query_environment_get, gWorkerCoreAssignment, timestampBase]
  · norm_num [Expression.eval, query_environment_get, gWorkerCoreAssignment,
      g_query_inverse64, timestampBase, babyBearModulus]
    have unit : (-2013265920 : ZMod babyBearModulus) = 1 := by
      calc
        _ = (-31457280 : ZMod babyBearModulus) * 64 := by ring
        _ = 1 := g_query_inverse64
    rw [unit]
    exact query_timestamp_nat 1 (by decide)

/-- One real controller query. The key and all seven outputs are transported
from controller_input; the56 controller rows are never substituted by fixtures. -/
private theorem g_worker_controller_query (variant : Variant) (index : Fin 56) :
    queryAt gWorkerCoreQueries 2
      (Verification.environment (workerAssignment variant index)) := by
  apply g_worker_core_query_of_thin variant index 2
  change queryAt gWorkerCoreQueries (2 : Nat)
    (Verification.environment (gWorkerCoreAssignment index))
  dsimp only [queryAt, gWorkerCoreQueries, Blake2G.importedConstraints,
    FlatOperation.lookups, List.getElem?_cons_zero, List.getElem?_cons_succ]
  dsimp only [Lookup.Contains, Table.toRaw, fromElements]
  rw [query_environment_data, Array.map_empty]
  apply g_query_of_eq (g_query_controller_lookup (Blake2G.controllerAt true index.val))
  -- Only the selected query's nine scalar fields are normalized. Control.step
  -- itself stays shared on both sides; no large controller data is evaluated.
  simp [Expression.eval, query_environment_get, gWorkerCoreAssignment,
    Blake2G.Control.Input.key, Blake2G.controllerAt, Nat.cast_add, add_comm]

/-- Every one of the18 actual XOR queries. Their native scalar operands and
outputs are zero in this fixture; each tag still selects its real imported row. -/
private theorem g_worker_xor_query (variant : Variant) (index : Fin 56) (slot : Fin 18) :
    queryAt gWorkerCoreQueries (3 + slot.val)
        (Verification.environment (workerAssignment variant index)) := by
  apply g_worker_core_query_of_thin variant index
    ⟨3 + slot.val, by have := slot.isLt; omega⟩
  fin_cases slot
  all_goals dsimp only [queryAt, gWorkerCoreQueries, Blake2G.importedConstraints,
    FlatOperation.lookups, List.getElem?_cons_zero, List.getElem?_cons_succ]
  all_goals dsimp only [Lookup.Contains, Table.toRaw, fromElements]
  all_goals rw [query_environment_data, Array.map_empty]
  all_goals solve
    | (apply g_query_of_eq (g_query_zero_lookup 0);
        norm_num [Expression.eval, query_environment_get, gWorkerCoreAssignment])
    | (apply g_query_of_eq (g_query_zero_lookup 1);
        norm_num [Expression.eval, query_environment_get, gWorkerCoreAssignment])
    | (apply g_query_of_eq (g_query_zero_lookup 2);
        norm_num [Expression.eval, query_environment_get, gWorkerCoreAssignment])
    | (apply g_query_of_eq (g_query_zero_lookup 3);
        norm_num [Expression.eval, query_environment_get, gWorkerCoreAssignment])
    | (apply g_query_of_eq (g_query_zero_lookup 4);
        norm_num [Expression.eval, query_environment_get, gWorkerCoreAssignment])

/-- All actual modeled G core queries, retaining both alignment lookups and
all19 real setup queries. No acceptance or arithmetic output is assumed. -/
theorem worker_queries (variant : Variant) (index : Fin 56) :
    ∀ lookup ∈ FlatOperation.lookups
      (Blake2G.importedConstraints (Blake2G.setupTable Blake2G.Control.controllerRows)),
      lookup.Contains (Verification.environment (workerAssignment variant index)) := by
  rw [List.forall_mem_iff_forall_getElem]
  intro query bound
  change query < gWorkerCoreQueries.length at bound
  have short : query < 21 := by simpa only [g_worker_core_query_count] using bound
  change Lookup.Contains (gWorkerCoreQueries[query]'bound)
    (Verification.environment (workerAssignment variant index))
  apply queryAt_getElem _ _ _ bound
  by_cases alignment : query < 2
  · exact g_worker_alignment_query variant index ⟨query, alignment⟩
  · by_cases controller : query = 2
    · subst query
      exact g_worker_controller_query variant index
    · let slot : Fin 18 := ⟨query - 3, by omega⟩
      have actual : 3 + slot.val = query := by dsimp [slot]; omega
      simpa only [actual] using g_worker_xor_query variant index slot


private theorem query_worker_invocation_of_clock (current : Nat) (row : Fin 228)
    (clock : current = 4 + 4 * row.val) :
    ((-503316480 : ZMod babyBearModulus) * ((current + 1 : Nat) : ZMod babyBearModulus) +
      503316480).val < timestampBase := by
  have quarter : (-503316480 : ZMod babyBearModulus) * 4 = 1 := by decide +kernel
  have actual : (-503316480 : ZMod babyBearModulus) *
      ((current + 1 : Nat) : ZMod babyBearModulus) + 503316480 =
        ((1 + row.val : Nat) : ZMod babyBearModulus) := by
    rw [clock]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    calc
      _ = ((-503316480 : ZMod babyBearModulus) * 4) *
          (1 + (row.val : ZMod babyBearModulus)) := by ring
      _ = _ := by rw [quarter]; ring
  rw [actual]
  apply query_timestamp_nat
  have rowBound := row.isLt
  dsimp [timestampBase]
  omega

/-- Opaque prior clocks prevent any chronological-ledger reduction while
normalizing the nine exact emitted low-comparison expressions. -/
private theorem query_worker_low_of_coordinates
    (assignment : Nat → ZMod babyBearModulus) (current : Nat) (prior : Fin 9 → Nat)
    (past : ∀ port : Fin 9, prior port < current + 3) (small : current + 3 < 916)
    (c1 : assignment 1 = ((current + 1 : Nat) : ZMod babyBearModulus))
    (previousLo : ∀ port : Fin 9, assignment (84 + 3 * port.val) = (prior port : ZMod babyBearModulus))
    (borrow : ∀ port : Fin 9, assignment (86 + 3 * port.val) = 1)
    (port : Fin 9) :
    queryAt (FlatOperation.lookups (Blake2G.importedConstraintsTimestampLookups
      (p := babyBearModulus))) (1 + 2 * port.val)
        (Verification.environment assignment) := by
  have negativeOne : ((Int.negSucc 0 : Int) : ZMod babyBearModulus) = -1 := by
    decide +kernel
  have negativeTwo : ((Int.negSucc 1 : Int) : ZMod babyBearModulus) = -2 := by
    decide +kernel
  have low := query_borrowed_low (current + 3) (prior port) (past port) small
  have previousValue := previousLo port
  have borrowed := borrow port
  fin_cases port
  all_goals norm_num only at previousValue borrowed
  all_goals dsimp only [queryAt, Blake2G.importedConstraintsTimestampLookups,
    FlatOperation.lookups, List.getElem?_cons_zero, List.getElem?_cons_succ]
  all_goals apply Trace.Proofs.range_contains
  all_goals simp only [Expression.eval, query_environment_get, c1, previousValue, borrowed,
    Nat.cast_add, negativeOne, negativeTwo]
  all_goals simp only [Nat.cast_add, Nat.cast_ofNat] at low
  all_goals
    refine lt_of_eq_of_lt (congrArg ZMod.val ?_) low
    ring

private theorem query_worker_high_of_coordinates
    (assignment : Nat → ZMod babyBearModulus)
    (c2 : assignment 2 = 0)
    (previousHi : ∀ port : Fin 9, assignment (85 + 3 * port.val) = 0)
    (borrow : ∀ port : Fin 9, assignment (86 + 3 * port.val) = 1)
    (port : Fin 9) :
    queryAt (FlatOperation.lookups (Blake2G.importedConstraintsTimestampLookups
      (p := babyBearModulus))) (2 + 2 * port.val)
        (Verification.environment assignment) := by
  have previousValue := previousHi port
  have borrowed := borrow port
  fin_cases port
  all_goals norm_num only at previousValue borrowed
  all_goals dsimp only [queryAt, Blake2G.importedConstraintsTimestampLookups,
    FlatOperation.lookups, List.getElem?_cons_zero, List.getElem?_cons_succ]
  all_goals apply Trace.Proofs.range_contains
  all_goals norm_num [Expression.eval, query_environment_get, c2, previousValue, borrowed,
    timestampBase, babyBearModulus]
  all_goals exact query_timestamp_nat 524287 (by decide)

private theorem query_worker_inverse64 : -(31457280 * 64 : ZMod babyBearModulus) = 1 := by
  decide +kernel

/-- All21 actual imported worker timestamp queries over abstract native
coordinates: invocation, nine low/high pairs, and both pointer alignments. -/
private theorem worker_timestamps_of_coordinates
    (assignment : Nat → ZMod babyBearModulus) (current : Nat) (prior : Fin 9 → Nat)
    (row : Fin 228) (clock : current = 4 + 4 * row.val)
    (past : ∀ port : Fin 9, prior port < current + 3) (small : current + 3 < 916)
    (c0 : assignment 0 = 1)
    (c1 : assignment 1 = ((current + 1 : Nat) : ZMod babyBearModulus))
    (c2 : assignment 2 = 0)
    (previousLo : ∀ port : Fin 9, assignment (84 + 3 * port.val) = (prior port : ZMod babyBearModulus))
    (previousHi : ∀ port : Fin 9, assignment (85 + 3 * port.val) = 0)
    (borrow : ∀ port : Fin 9, assignment (86 + 3 * port.val) = 1)
    (c13 : assignment 13 = 0) (c31 : assignment 31 = 64) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment assignment)
      Blake2G.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [Blake2G.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro query bound
    have short : query < 21 := by simpa only [Blake2G.timestamp_count] using bound
    apply queryAt_getElem _ _ _ bound
    by_cases invocation : query = 0
    · subst query
      dsimp only [queryAt, Blake2G.importedConstraintsTimestampLookups, FlatOperation.lookups,
        List.getElem?_cons_zero, List.getElem?_cons_succ]
      apply Trace.Proofs.range_contains
      simpa [Expression.eval, query_environment_get, c0, c1,
        sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        using query_worker_invocation_of_clock current row clock
    · by_cases comparison : query < 19
      · let port : Fin 9 := ⟨(query - 1) / 2, by omega⟩
        have positions : query = 1 + 2 * port.val ∨ query = 2 + 2 * port.val := by
          dsimp [port]
          omega
        rcases positions with low | high
        · simpa only [← low] using
            query_worker_low_of_coordinates assignment current prior past small c1 previousLo borrow port
        · simpa only [← high] using
            query_worker_high_of_coordinates assignment c2 previousHi borrow port
      · have alignment : query = 19 ∨ query = 20 := by omega
        rcases alignment with rfl | rfl
        all_goals dsimp only [queryAt, Blake2G.importedConstraintsTimestampLookups,
          FlatOperation.lookups, List.getElem?_cons_zero, List.getElem?_cons_succ]
        all_goals apply Trace.Proofs.range_contains
        · norm_num [Expression.eval, query_environment_get, c13, timestampBase, babyBearModulus]
        · norm_num [Expression.eval, query_environment_get, c31,
            timestampBase, babyBearModulus]
          have unit : (-2013265920 : ZMod babyBearModulus) = 1 := by
            calc
              _ = -(31457280 * 64 : ZMod babyBearModulus) := by ring
              _ = 1 := query_worker_inverse64
          rw [unit]
          exact query_timestamp_nat 1 (by decide)

/-- Actual worker timestamps are obtained from exact native coordinates and
already proved chronological bounds. The prior-clock function stays opaque. -/
theorem worker_timestamps (variant : Variant) (index : Fin 56) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (workerAssignment variant index))
      Blake2G.importedConstraintsTimestampLookups := by
  apply worker_timestamps_of_coordinates (workerAssignment variant index)
    (callStart index) (workerReadStamp variant index) (callRow index)
  · rfl
  · exact worker_previous_before_current variant index
  · exact current_worker_clock_bound index
  · rfl
  · change (callStart index : ZMod babyBearModulus) + 1 =
      ((callStart index + 1 : Nat) : ZMod babyBearModulus)
    simp only [Nat.cast_add, Nat.cast_one]
  · rfl
  · intro port
    fin_cases port <;> rfl
  · intro port
    fin_cases port <;> rfl
  · intro port
    fin_cases port <;> rfl
  · rfl
  · rfl

private def request_cpu (variant : Variant) (index : Fin 228) :
    Row babyBearModulus UnifiedFamily := ⟨.machine, machineAssignment variant index⟩

private theorem request_start (variant : Variant) (index : Fin 228) :
    (request_cpu variant index).start =
      ⟨(((codeEntry variant (rowCodeIndex index)).pc.toNat : ZMod babyBearModulus), 0),
        ((machineClock index : Nat), 0)⟩ := by
  rfl

private theorem request_finish (variant : Variant) (index : Fin 228) :
    (request_cpu variant index).finish =
      ⟨((nextPC index : ZMod babyBearModulus), 0), ((machineClock index + 4 : Nat), 0)⟩ := by
  exact congrArg (fun timestamp =>
    (⟨((nextPC index : ZMod babyBearModulus), 0), timestamp⟩ : PCState.State babyBearModulus))
    (machine_native_timing variant index).2

private theorem request_code_pc (variant : Variant) (entry : Fin 12) :
    (codeEntry variant entry).pc.toNat = (codeEntry .baseline entry).pc.toNat := by
  fin_cases entry <;> cases variant <;> rfl

private theorem request_next_pc : ∀ index : Fin 227,
    nextPC index.castSucc = (codeEntry .baseline (rowCodeIndex index.succ)).pc.toNat := by
  have checked : (List.finRange 227).all (fun index => decide
      (nextPC index.castSucc = (codeEntry .baseline (rowCodeIndex index.succ)).pc.toNat)) = true := by
    decide +kernel
  intro index
  exact of_decide_eq_true (List.all_eq_true.mp checked index (List.mem_finRange index))

private theorem request_successor (variant : Variant) (index : Fin 227) :
    (request_cpu variant index.castSucc).finish = (request_cpu variant index.succ).start := by
  have clock : machineClock index.castSucc + 4 = machineClock index.succ := by
    change 4 + 4 * index.val + 4 = 4 + 4 * (index.val + 1)
    omega
  rw [request_finish, request_start, request_code_pc, ← request_next_pc, clock]

/-- The list identity is structural. Only the small native PC/time projections
and the finite public PC path are evaluated, never the full assignment list. -/
private theorem machine_state_chain (variant : Variant) :
    (data variant).machine.initial :: (data variant).machine.rows.map Trace.Row.finish =
      (data variant).machine.rows.map Trace.Row.start ++ [(data variant).machine.terminal] := by
  have starts : (List.finRange 228).map (fun index => (request_cpu variant index).start) =
      (request_cpu variant 0).start ::
        (List.finRange 227).map (fun index => (request_cpu variant index.succ).start) := by
    simpa only [List.map_cons, List.map_map, Function.comp_def] using
      congrArg (List.map (fun index : Fin 228 => (request_cpu variant index).start))
        (List.finRange_succ (n := 227))
  have lastIndex : Fin.last 227 = (227 : Fin 228) := by
    apply Fin.ext
    rfl
  have finishes : (List.finRange 228).map (fun index => (request_cpu variant index).finish) =
      (List.finRange 227).map (fun index => (request_cpu variant index.castSucc).finish) ++
        [(request_cpu variant 227).finish] := by
    simpa only [List.map_append, List.map_map, List.map_cons, List.map_nil, Function.comp_def, lastIndex] using
      congrArg (List.map (fun index : Fin 228 => (request_cpu variant index).finish))
        (List.finRange_succ_last (n := 227))
  have middle : (List.finRange 227).map (fun index => (request_cpu variant index.castSucc).finish) =
      (List.finRange 227).map (fun index => (request_cpu variant index.succ).start) := by
    apply List.map_congr_left
    intro index _
    exact request_successor variant index
  have first : (request_cpu variant 0).start = (data variant).machine.initial := by rfl
  have last : (request_cpu variant 227).finish = (data variant).machine.terminal := by rfl
  change (data variant).machine.initial ::
      ((List.finRange 228).map (request_cpu variant)).map Trace.Row.finish =
    ((List.finRange 228).map (request_cpu variant)).map Trace.Row.start ++
      [(data variant).machine.terminal]
  simp only [List.map_map, Function.comp_def]
  rw [finishes, starts, middle, first, last]
  rfl

theorem machine_states (variant : Variant) :
    ((data variant).machine.initial :: (data variant).machine.rows.map Trace.Row.finish).Perm
      ((data variant).machine.terminal :: (data variant).machine.rows.map Trace.Row.start) := by
  rw [machine_state_chain]
  exact List.perm_append_comm

private theorem request_call_indices :
    ((List.finRange 228).filter isCaller) = (List.finRange 56).map callRow := by
  decide +kernel

/-- Only index selection is computed. The native filter is transported through
its map using the proved selector equivalence and retains exact multiplicity. -/
theorem callers_exact (variant : Variant) :
    (data variant).callers = (List.finRange 56).map fun index =>
      (⟨.machine, machineAssignment variant (callRow index)⟩ : Row babyBearModulus UnifiedFamily) := by
  change ((List.finRange 228).map (request_cpu variant)).filter
      (fun row => decide (UnifiedReduced.Caller.Selected row.assignment)) = _
  rw [List.filter_map]
  have predicate : ((fun row : Row babyBearModulus UnifiedFamily =>
      decide (UnifiedReduced.Caller.Selected row.assignment)) ∘ request_cpu variant) = isCaller := by
    funext index
    apply Bool.eq_iff_iff.mpr
    simpa only [Function.comp_def, request_cpu, decide_eq_true_eq] using
      native_selected_iff variant index
  rw [predicate, request_call_indices]
  simp only [List.map_map, Function.comp_def, request_cpu]

/-- Decoder-column stencil only. The query projection below proves agreement
on every used column; unused clock/history columns are omitted from reduction. -/
private def request_decoder_assignment (variant : Variant) (entry : Fin 12)
    (column : Nat) : ZMod babyBearModulus :=
  let called := decide (entry.val = 6 ∨ entry.val = 11)
  let fields := if called then
      (Tests.DelegationCaller.entry .blakeG).data.mapFamily (fun _ => .machine)
    else (UnifiedReduced.decoderFields (codeEntry variant entry).instruction).getD
      ⟨.machine, 0, 0, 0, ⟨0, 0⟩, 0, 0⟩
  if column = 0 then (codeEntry variant entry).pc.toNat
  else if column = 2 then 0
  else if column = 4 then 1
  else if column = 5 then fields.rs1.toNat
  else if column = 6 then if called then 0x7c8 else fields.rs2.toNat
  else if column = 7 then fields.rd.toNat
  else if column = 8 then fields.immediate.lo
  else if column = 9 then fields.immediate.hi
  else if column = 10 then fields.funct3
  else if 11 ≤ column ∧ column ≤ 29 then if fields.mask.testBit (column - 11) then 1 else 0
  else 0

private theorem request_decoder_projection (variant : Variant) (index : Fin 228) :
    UnifiedReduced.decoderQuery (machineAssignment variant index) =
      UnifiedReduced.decoderQuery (request_decoder_assignment variant (rowCodeIndex index)) := by
  rfl

private theorem request_caller_code (variant : Variant) (entry : Fin 12)
    (selected : decide (entry.val = 6 ∨ entry.val = 11) = true) :
    (UnifiedReduced.Caller.decoderTable callerProgram).Contains #[]
      (UnifiedReduced.decoderQuery (request_decoder_assignment variant entry)) := by
  have choices := of_decide_eq_true selected
  rcases choices with first | last
  · have equal : entry = 6 := Fin.ext first
    subst entry
    exact ⟨(0 : Fin 2), by cases variant <;> decide +kernel⟩
  · have equal : entry = 11 := Fin.ext last
    subst entry
    exact ⟨(1 : Fin 2), by cases variant <;> decide +kernel⟩

/-- Canonical UnifiedReduced query, with the actual imported nine columns. -/
theorem caller_decoded (variant : Variant) :
    ∀ row ∈ (data variant).callers,
      (UnifiedReduced.Caller.decoderTable (data variant).program).Contains #[]
        (UnifiedReduced.decoderQuery row.assignment) := by
  intro row member
  obtain ⟨included, selected⟩ := List.mem_filter.mp member
  change row ∈ machineRows variant at included
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp included
  have called : isCaller index = true :=
    (native_selected_iff variant index).mp (of_decide_eq_true selected)
  rw [request_decoder_projection]
  exact request_caller_code variant (rowCodeIndex index) called

private theorem request_at_call (variant : Variant) (index : Fin 56) :
    UnifiedReduced.Caller.request (machineAssignment variant (callRow index)) =
      Delegation.Requests.fulfillment
        (⟨.blakeG, workerAssignment variant index⟩ : Delegation.Row babyBearModulus) := by
  fin_cases index <;> cases variant <;> rfl

private theorem request_lists_equal (variant : Variant) :
    (data variant).calls = (data variant).fulfillments := by
  unfold UnifiedReduced.Caller.RequestTrace.calls UnifiedReduced.Caller.RequestTrace.fulfillments
  rw [callers_exact]
  change ((List.finRange 56).map fun index =>
      UnifiedReduced.Caller.request (machineAssignment variant (callRow index))) =
    ((List.finRange 56).map fun index => Delegation.Requests.fulfillment
      (⟨.blakeG, workerAssignment variant index⟩ : Delegation.Row babyBearModulus))
  apply List.map_congr_left
  intro index _
  exact request_at_call variant index

theorem request_matching (variant : Variant) :
    Delegation.Requests.Matching (data variant).calls (data variant).fulfillments := by
  unfold Delegation.Requests.Matching
  rw [← request_lists_equal variant]
  exact List.perm_append_comm

private theorem request_ordinary_code (variant : Variant) (entry : Fin 12)
    (ordinary : decide (entry.val = 6 ∨ entry.val = 11) = false) :
    (UnifiedReduced.decoderTable (ordinaryProgram variant)).Contains #[]
      (UnifiedReduced.decoderQuery (request_decoder_assignment variant entry)) := by
  fin_cases entry <;> cases variant
  all_goals solve
    | exact Bool.noConfusion ordinary
    | exact ⟨(0 : Fin 10), by decide +kernel⟩
    | exact ⟨(1 : Fin 10), by decide +kernel⟩
    | exact ⟨(2 : Fin 10), by decide +kernel⟩
    | exact ⟨(3 : Fin 10), by decide +kernel⟩
    | exact ⟨(4 : Fin 10), by decide +kernel⟩
    | exact ⟨(5 : Fin 10), by decide +kernel⟩
    | exact ⟨(6 : Fin 10), by decide +kernel⟩
    | exact ⟨(7 : Fin 10), by decide +kernel⟩
    | exact ⟨(8 : Fin 10), by decide +kernel⟩
    | exact ⟨(9 : Fin 10), by decide +kernel⟩

theorem ordinary_decoded (variant : Variant) :
    ∀ row ∈ (data variant).machine.rows, row ∉ (data variant).callers →
      (UnifiedReduced.decoderTable (ordinaryProgram variant)).Contains #[] row.decoderQuery := by
  intro row member noncaller
  change row ∈ machineRows variant at member
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  have included : request_cpu variant index ∈ (data variant).machine.rows :=
    List.mem_map.mpr ⟨index, List.mem_finRange _, rfl⟩
  have ordinary : isCaller index = false := by
    cases called : isCaller index with
    | false => rfl
    | true =>
      exact False.elim (noncaller (List.mem_filter.mpr ⟨included,
        decide_eq_true ((native_selected_iff variant index).mpr called)⟩))
  change (UnifiedReduced.decoderTable (ordinaryProgram variant)).Contains #[]
    (UnifiedReduced.decoderQuery (machineAssignment variant index))
  rw [request_decoder_projection]
  exact request_ordinary_code variant (rowCodeIndex index) ordinary

end Tests.PathGLoopNative
