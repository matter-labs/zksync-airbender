import Airbender.Proofs.GKRProtocol.ProgramShiftTags
import Airbender.Proofs.GKRProtocol.ProgramDecoderLookup.ShiftBinopCached
import Airbender.Proofs.GKRProtocol.ProgramFixedLookup.ShiftBinopCached

namespace Airbender.Compiler.ProgramConstraintsNative.ShiftBinopCached
open Airbender Airbender.Compiler Airbender.Compiler.PooledRowNative.ShiftBinopCached
open Airbender.Compiler.PhysicalClosedNative.ShiftBinopCached
set_option warningAsError true
set_option Elab.async false

/-- The five helper requests use fixed tags, not decoder or ROM tags. -/
def FixedHelperTags (input : Input) : Prop :=
  ∀ index : Fin 5,
    let query := Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.genericQueries.get
      ⟨index.val, by have small := index.isLt; change index.val < 6; omega⟩
    let tag := (query.fields.map (fun field => field.value
      ((input.physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘
        Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement))).getLast?.getD 0
    tag ≠ 0 ∧ tag ≠ 46 ∧ tag ≠ 34

/-- Public program decoding and native arithmetic derive all helper tags. -/
theorem helper_guards
    {config : Trace.NativeDecoder.ProgramRows.Config} {initial : Reference.RiscV.Sail.State}
    {text : List (BitVec 32)} {capacity : Nat}
    {masks : Trace.PooledFamily → Trace.NativeDecoder.ProgramRows.Mask}
    {columns : Trace.PooledFamily → List (List Source.BaseField)}
    (programSetup : UnrolledProgramSetup config initial text capacity masks columns)
    (input : Input)
    (arguments : LookupArgumentsWith (fun group index =>
      NativeProgramSetup.unrolledLookupRows initial columns .shiftBinopCached group index.val) input)
    (typed : (inputRow input).decoderQuery[0].val < 65536) : FixedHelperTags input := by
  have matched := ProgramDecoderLookup.ShiftBinopCached.decoder_lookup programSetup input arguments typed
  have assertions : ∀ expression ∈ FlatOperation.constraints
      (ShiftBinop.importedConstraints (p := babyBearModulus)),
      expression.eval (Verification.environment (inputRow input).assignment) = 0 := by
    rw [Airbender.Compiler.CleanLinksNative.ShiftBinopCached.arithmetic_inventory]
    exact CleanExpression.assertions_only _ _
      (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.arithmetic_preserved input.physical (fun _ _ => #[]) input.arithmetic)
  have tags := public_shift_helper_tags programSetup (inputRow input).assignment matched typed assertions
  have tagEquations := shift_tag_equations_of_assertions assertions
  have firstTag : (8 * (inputRow input).assignment 11 + 3 * (inputRow input).assignment 12 ≠ 0) ∧
      (8 * (inputRow input).assignment 11 + 3 * (inputRow input).assignment 12 ≠ 46) ∧
      (8 * (inputRow input).assignment 11 + 3 * (inputRow input).assignment 12 ≠ 34) := by
    rcases tags.1 with selected | selected
    all_goals rw [selected]; exact of_decide_eq_true rfl
  have otherTag : (9 * (inputRow input).assignment 11 + (inputRow input).assignment 10 * (inputRow input).assignment 12 ≠ 0) ∧
      (9 * (inputRow input).assignment 11 + (inputRow input).assignment 10 * (inputRow input).assignment 12 ≠ 46) ∧
      (9 * (inputRow input).assignment 11 + (inputRow input).assignment 10 * (inputRow input).assignment 12 ≠ 34) := by
    rcases tags.2 with selected | selected | selected | selected
    all_goals rw [selected]; exact of_decide_eq_true rfl
  intro index
  fin_cases index
  · have same : (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression0_9).eval
        (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical (fun _ _ => #[])) =
        (((Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.genericQueries.get ⟨0, by decide⟩).fields.map (fun field => field.value
          ((input.physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘
            Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement))).getLast?.getD 0) :=
      Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value0_9 input.physical (fun _ _ => #[]) input.arithmetic
    dsimp only
    rw [← same]
    simp [Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression0_9, _root_.Expression.eval]
    change (inputRow input).assignment 55 ≠ 0 ∧
      (inputRow input).assignment 55 ≠ 46 ∧
      (inputRow input).assignment 55 ≠ 34
    have equation : (inputRow input).assignment 55 =
        8 * (inputRow input).assignment 11 + 3 * (inputRow input).assignment 12 :=
      tagEquations.1
    rw [equation]
    exact firstTag
  · have same : (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression1_9).eval
        (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical (fun _ _ => #[])) =
        (((Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.genericQueries.get ⟨1, by decide⟩).fields.map (fun field => field.value
          ((input.physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘
            Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement))).getLast?.getD 0) :=
      Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value1_9 input.physical (fun _ _ => #[]) input.arithmetic
    dsimp only
    rw [← same]
    simp [Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression1_9, _root_.Expression.eval]
    change (inputRow input).assignment 64 ≠ 0 ∧
      (inputRow input).assignment 64 ≠ 46 ∧
      (inputRow input).assignment 64 ≠ 34
    have equation : (inputRow input).assignment 64 =
        9 * (inputRow input).assignment 11 + (inputRow input).assignment 10 * (inputRow input).assignment 12 :=
      tagEquations.2 ⟨0, by decide⟩
    rw [equation]
    exact otherTag
  · have same : (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression2_9).eval
        (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical (fun _ _ => #[])) =
        (((Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.genericQueries.get ⟨2, by decide⟩).fields.map (fun field => field.value
          ((input.physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘
            Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement))).getLast?.getD 0) :=
      Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value2_9 input.physical (fun _ _ => #[]) input.arithmetic
    dsimp only
    rw [← same]
    simp [Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression2_9, _root_.Expression.eval]
    change (inputRow input).assignment 73 ≠ 0 ∧
      (inputRow input).assignment 73 ≠ 46 ∧
      (inputRow input).assignment 73 ≠ 34
    have equation : (inputRow input).assignment 73 =
        9 * (inputRow input).assignment 11 + (inputRow input).assignment 10 * (inputRow input).assignment 12 :=
      tagEquations.2 ⟨1, by decide⟩
    rw [equation]
    exact otherTag
  · have same : (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression3_9).eval
        (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical (fun _ _ => #[])) =
        (((Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.genericQueries.get ⟨3, by decide⟩).fields.map (fun field => field.value
          ((input.physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘
            Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement))).getLast?.getD 0) :=
      Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value3_9 input.physical (fun _ _ => #[]) input.arithmetic
    dsimp only
    rw [← same]
    simp [Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression3_9, _root_.Expression.eval]
    change (inputRow input).assignment 82 ≠ 0 ∧
      (inputRow input).assignment 82 ≠ 46 ∧
      (inputRow input).assignment 82 ≠ 34
    have equation : (inputRow input).assignment 82 =
        9 * (inputRow input).assignment 11 + (inputRow input).assignment 10 * (inputRow input).assignment 12 :=
      tagEquations.2 ⟨2, by decide⟩
    rw [equation]
    exact otherTag
  · have same : (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression4_9).eval
        (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical (fun _ _ => #[])) =
        (((Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.genericQueries.get ⟨4, by decide⟩).fields.map (fun field => field.value
          ((input.physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘
            Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement))).getLast?.getD 0) :=
      Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value4_9 input.physical (fun _ _ => #[]) input.arithmetic
    dsimp only
    rw [← same]
    simp [Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression4_9, _root_.Expression.eval]
    change (inputRow input).assignment 91 ≠ 0 ∧
      (inputRow input).assignment 91 ≠ 46 ∧
      (inputRow input).assignment 91 ≠ 34
    have equation : (inputRow input).assignment 91 =
        9 * (inputRow input).assignment 11 + (inputRow input).assignment 10 * (inputRow input).assignment 12 :=
      tagEquations.2 ⟨3, by decide⟩
    rw [equation]
    exact otherTag

private theorem range_lookup0
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .shiftBinopCached group index.val) input) (data : ProverData Source.BaseField) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.rangeExpression0).Contains (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.range16Queries.get ⟨0, by decide⟩
  have member := ProgramFixedLookup.ShiftBinopCached.range_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.range16Queries ⟨0, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.ShiftBinopCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.ShiftBinopCached.native.field5_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.range_value0 input.physical data input.arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.ShiftBinopCached.native.range16_clean_refinement _ valid _

private theorem range_lookup1
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .shiftBinopCached group index.val) input) (data : ProverData Source.BaseField) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.rangeExpression1).Contains (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.range16Queries.get ⟨1, by decide⟩
  have member := ProgramFixedLookup.ShiftBinopCached.range_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.range16Queries ⟨1, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.ShiftBinopCached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.ShiftBinopCached.native.field6_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.range_value1 input.physical data input.arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.ShiftBinopCached.native.range16_clean_refinement _ valid _

private theorem generic_lookup0
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .shiftBinopCached group index.val) input) (guards : FixedHelperTags input) (data : ProverData Source.BaseField) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.genericExpressions0).Contains (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.genericQueries.get ⟨0, by decide⟩
  have member := ProgramFixedLookup.ShiftBinopCached.generic_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.genericQueries ⟨0, by decide⟩) (guards ⟨0, by decide⟩).1 (guards ⟨0, by decide⟩).2.1 (guards ⟨0, by decide⟩).2.2
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value0_0 input.physical data input.arithmetic)
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value0_1 input.physical data input.arithmetic)
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value0_2 input.physical data input.arithmetic)
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value0_3 input.physical data input.arithmetic)
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value0_4 input.physical data input.arithmetic)
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value0_5 input.physical data input.arithmetic)
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value0_6 input.physical data input.arithmetic)
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value0_7 input.physical data input.arithmetic)
  have same8 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value0_8 input.physical data input.arithmetic)
  have same9 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value0_9 input.physical data input.arithmetic)
  apply clean_vector_lookup
  apply ShiftSetupNative.clean_contains _ ?_ ?_ _
  · simp only [Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.genericExpressions0, Vector.map_mk, List.map_toArray]
    change Airbender.Compiler.MaterializedNative.ShiftBinopCached.native.model.Contains Airbender.Compiler.TableNative.ShiftBinopCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression0_0.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression0_1.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression0_2.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression0_3.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression0_4.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression0_5.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression0_6.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression0_7.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression0_8.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression0_9.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data)]
    rw [same0, same1, same2, same3, same4, same5, same6, same7, same8, same9]
    exact valid
  · rw [Vector.getElem_map]
    change Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression0_8.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data) = 0
    rw [same8]
    rfl


private theorem generic_lookup1
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .shiftBinopCached group index.val) input) (guards : FixedHelperTags input) (data : ProverData Source.BaseField) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.genericExpressions1).Contains (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.genericQueries.get ⟨1, by decide⟩
  have member := ProgramFixedLookup.ShiftBinopCached.generic_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.genericQueries ⟨1, by decide⟩) (guards ⟨1, by decide⟩).1 (guards ⟨1, by decide⟩).2.1 (guards ⟨1, by decide⟩).2.2
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value1_0 input.physical data input.arithmetic)
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value1_1 input.physical data input.arithmetic)
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value1_2 input.physical data input.arithmetic)
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value1_3 input.physical data input.arithmetic)
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value1_4 input.physical data input.arithmetic)
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value1_5 input.physical data input.arithmetic)
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value1_6 input.physical data input.arithmetic)
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value1_7 input.physical data input.arithmetic)
  have same8 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value1_8 input.physical data input.arithmetic)
  have same9 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value1_9 input.physical data input.arithmetic)
  apply clean_vector_lookup
  apply ShiftSetupNative.clean_contains _ ?_ ?_ _
  · simp only [Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.genericExpressions1, Vector.map_mk, List.map_toArray]
    change Airbender.Compiler.MaterializedNative.ShiftBinopCached.native.model.Contains Airbender.Compiler.TableNative.ShiftBinopCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression1_0.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression1_1.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression1_2.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression1_3.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression1_4.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression1_5.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression1_6.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression1_7.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression1_8.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression1_9.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data)]
    rw [same0, same1, same2, same3, same4, same5, same6, same7, same8, same9]
    exact valid
  · rw [Vector.getElem_map]
    change Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression1_8.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data) = 0
    rw [same8]
    rfl


private theorem generic_lookup2
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .shiftBinopCached group index.val) input) (guards : FixedHelperTags input) (data : ProverData Source.BaseField) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.genericExpressions2).Contains (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.genericQueries.get ⟨2, by decide⟩
  have member := ProgramFixedLookup.ShiftBinopCached.generic_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.genericQueries ⟨2, by decide⟩) (guards ⟨2, by decide⟩).1 (guards ⟨2, by decide⟩).2.1 (guards ⟨2, by decide⟩).2.2
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value2_0 input.physical data input.arithmetic)
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value2_1 input.physical data input.arithmetic)
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value2_2 input.physical data input.arithmetic)
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value2_3 input.physical data input.arithmetic)
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value2_4 input.physical data input.arithmetic)
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value2_5 input.physical data input.arithmetic)
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value2_6 input.physical data input.arithmetic)
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value2_7 input.physical data input.arithmetic)
  have same8 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value2_8 input.physical data input.arithmetic)
  have same9 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value2_9 input.physical data input.arithmetic)
  apply clean_vector_lookup
  apply ShiftSetupNative.clean_contains _ ?_ ?_ _
  · simp only [Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.genericExpressions2, Vector.map_mk, List.map_toArray]
    change Airbender.Compiler.MaterializedNative.ShiftBinopCached.native.model.Contains Airbender.Compiler.TableNative.ShiftBinopCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression2_0.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression2_1.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression2_2.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression2_3.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression2_4.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression2_5.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression2_6.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression2_7.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression2_8.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression2_9.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data)]
    rw [same0, same1, same2, same3, same4, same5, same6, same7, same8, same9]
    exact valid
  · rw [Vector.getElem_map]
    change Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression2_8.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data) = 0
    rw [same8]
    rfl


private theorem generic_lookup3
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .shiftBinopCached group index.val) input) (guards : FixedHelperTags input) (data : ProverData Source.BaseField) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.genericExpressions3).Contains (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.genericQueries.get ⟨3, by decide⟩
  have member := ProgramFixedLookup.ShiftBinopCached.generic_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.genericQueries ⟨3, by decide⟩) (guards ⟨3, by decide⟩).1 (guards ⟨3, by decide⟩).2.1 (guards ⟨3, by decide⟩).2.2
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value3_0 input.physical data input.arithmetic)
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value3_1 input.physical data input.arithmetic)
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value3_2 input.physical data input.arithmetic)
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value3_3 input.physical data input.arithmetic)
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value3_4 input.physical data input.arithmetic)
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value3_5 input.physical data input.arithmetic)
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value3_6 input.physical data input.arithmetic)
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value3_7 input.physical data input.arithmetic)
  have same8 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value3_8 input.physical data input.arithmetic)
  have same9 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value3_9 input.physical data input.arithmetic)
  apply clean_vector_lookup
  apply ShiftSetupNative.clean_contains _ ?_ ?_ _
  · simp only [Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.genericExpressions3, Vector.map_mk, List.map_toArray]
    change Airbender.Compiler.MaterializedNative.ShiftBinopCached.native.model.Contains Airbender.Compiler.TableNative.ShiftBinopCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression3_0.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression3_1.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression3_2.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression3_3.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression3_4.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression3_5.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression3_6.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression3_7.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression3_8.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression3_9.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data)]
    rw [same0, same1, same2, same3, same4, same5, same6, same7, same8, same9]
    exact valid
  · rw [Vector.getElem_map]
    change Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression3_8.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data) = 0
    rw [same8]
    rfl


private theorem generic_lookup4
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .shiftBinopCached group index.val) input) (guards : FixedHelperTags input) (data : ProverData Source.BaseField) :
    (Lookup.mk nativeSetup.toRaw Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.genericExpressions4).Contains (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.genericQueries.get ⟨4, by decide⟩
  have member := ProgramFixedLookup.ShiftBinopCached.generic_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.genericQueries ⟨4, by decide⟩) (guards ⟨4, by decide⟩).1 (guards ⟨4, by decide⟩).2.1 (guards ⟨4, by decide⟩).2.2
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.ShiftBinopCached.native.bank.address) ∘ Airbender.Compiler.LookupNative.ShiftBinopCached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid := member nonzero
  have same0 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value4_0 input.physical data input.arithmetic)
  have same1 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value4_1 input.physical data input.arithmetic)
  have same2 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value4_2 input.physical data input.arithmetic)
  have same3 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value4_3 input.physical data input.arithmetic)
  have same4 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value4_4 input.physical data input.arithmetic)
  have same5 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value4_5 input.physical data input.arithmetic)
  have same6 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value4_6 input.physical data input.arithmetic)
  have same7 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value4_7 input.physical data input.arithmetic)
  have same8 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value4_8 input.physical data input.arithmetic)
  have same9 := (Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.generic_value4_9 input.physical data input.arithmetic)
  apply clean_vector_lookup
  apply ShiftSetupNative.clean_contains _ ?_ ?_ _
  · simp only [Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.genericExpressions4, Vector.map_mk, List.map_toArray]
    change Airbender.Compiler.MaterializedNative.ShiftBinopCached.native.model.Contains Airbender.Compiler.TableNative.ShiftBinopCached.native.genericSetupColumns [Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression4_0.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression4_1.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression4_2.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression4_3.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression4_4.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression4_5.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression4_6.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression4_7.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression4_8.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data), Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression4_9.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data)]
    rw [same0, same1, same2, same3, same4, same5, same6, same7, same8, same9]
    exact valid
  · rw [Vector.getElem_map]
    change Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopCached.native.part0.genericExpression4_8.eval (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical data) = 0
    rw [same8]
    rfl


/-- Native CPU constraints hold for any public program setup rows. -/
theorem input_constraints
    {config : Trace.NativeDecoder.ProgramRows.Config} {initial : Reference.RiscV.Sail.State}
    {text : List (BitVec 32)} {capacity : Nat}
    {masks : Trace.PooledFamily → Trace.NativeDecoder.ProgramRows.Mask}
    {columns : Trace.PooledFamily → List (List Source.BaseField)}
    (programSetup : UnrolledProgramSetup config initial text capacity masks columns)
    (input : Input)
    (arguments : LookupArgumentsWith (fun group index =>
      NativeProgramSetup.unrolledLookupRows initial columns .shiftBinopCached group index.val) input)
    (typed : (inputRow input).decoderQuery[0].val < 65536) (setup : Trace.PooledSetup babyBearModulus) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (inputRow input).assignment)
      ((inputRow input).constraints setup) := by
  have helpers := ProgramFixedLookup.ShiftBinopCached.helpers_from_arguments
    (NativeProgramSetup.unrolledDecoderColumns columns) (Trace.ROM.words initial) input arguments
  have guards := helper_guards programSetup input arguments typed
  apply Airbender.Compiler.CleanLinksNative.ShiftBinopCached.retained_clock_constraints input.physical (fun _ _ => #[]) input.arithmetic
  rw [Airbender.Compiler.PhysicalClosedNative.ShiftBinopCached.clock_lookup_inventory]
  exact PredicateChecks.all (PredicateChecks.cons (range_lookup0 (NativeProgramSetup.unrolledDecoderColumns columns) (Trace.ROM.words initial) input arguments (fun _ _ => #[])) (PredicateChecks.cons (range_lookup1 (NativeProgramSetup.unrolledDecoderColumns columns) (Trace.ROM.words initial) input arguments (fun _ _ => #[])) (PredicateChecks.cons (generic_lookup0 (NativeProgramSetup.unrolledDecoderColumns columns) (Trace.ROM.words initial) input arguments guards (fun _ _ => #[])) (PredicateChecks.cons (generic_lookup1 (NativeProgramSetup.unrolledDecoderColumns columns) (Trace.ROM.words initial) input arguments guards (fun _ _ => #[])) (PredicateChecks.cons (generic_lookup2 (NativeProgramSetup.unrolledDecoderColumns columns) (Trace.ROM.words initial) input arguments guards (fun _ _ => #[])) (PredicateChecks.cons (generic_lookup3 (NativeProgramSetup.unrolledDecoderColumns columns) (Trace.ROM.words initial) input arguments guards (fun _ _ => #[])) (PredicateChecks.cons (generic_lookup4 (NativeProgramSetup.unrolledDecoderColumns columns) (Trace.ROM.words initial) input arguments guards (fun _ _ => #[])) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.timestampExpression0 (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.timestamp_bound0 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.timestampExpression1 (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.timestamp_bound1 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.timestampExpression2 (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.timestamp_bound2 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.timestampExpression3 (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.timestamp_bound3 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.timestampExpression4 (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.timestamp_bound4 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.timestampExpression5 (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.timestamp_bound5 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.timestampExpression6 (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.timestamp_bound6 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.timestampExpression7 (Airbender.Compiler.CleanArithmeticNative.ShiftBinopCached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.ShiftBinopCached.native.timestamp_bound7 input.physical (fun _ _ => #[]) input.arithmetic helpers)) PredicateChecks.nil)))))))))))))))

end Airbender.Compiler.ProgramConstraintsNative.ShiftBinopCached
