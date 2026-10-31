import Airbender.Proofs.GKRProtocol.ProgramFixedLookup.UnifiedUncached
import Airbender.Proofs.GKRProtocol.ProgramDecoderLookup.UnifiedUncached
import Airbender.Proofs.GKRProtocol.ProgramUnifiedDecoderTags
import Airbender.Proofs.GKRProtocol.ProgramUnifiedArithmeticTags
import Airbender.Proofs.GKRProtocol.ProgramUnifiedROM

namespace Airbender.Compiler.ProgramConstraintsNative.UnifiedUncached
open Airbender Airbender.Compiler Airbender.Compiler.UnifiedRowNative.UnifiedUncached
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536

private theorem range_lookup0
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .unifiedUncached group index.val) input) (data : ProverData Source.BaseField) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.rangeExpression0).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries.get ⟨0, by decide⟩
  have member := ProgramFixedLookup.UnifiedUncached.range_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries ⟨0, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.UnifiedUncached.native.field5_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.range_value0 input.physical data input.arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.UnifiedUncached.native.range16_clean_refinement _ valid _

private theorem range_lookup1
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .unifiedUncached group index.val) input) (data : ProverData Source.BaseField) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.rangeExpression1).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries.get ⟨1, by decide⟩
  have member := ProgramFixedLookup.UnifiedUncached.range_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries ⟨1, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.UnifiedUncached.native.field6_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.range_value1 input.physical data input.arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.UnifiedUncached.native.range16_clean_refinement _ valid _

private theorem range_lookup2
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .unifiedUncached group index.val) input) (data : ProverData Source.BaseField) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.rangeExpression2).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries.get ⟨2, by decide⟩
  have member := ProgramFixedLookup.UnifiedUncached.range_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries ⟨2, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.UnifiedUncached.native.field7_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.range_value2 input.physical data input.arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.UnifiedUncached.native.range16_clean_refinement _ valid _

private theorem range_lookup3
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .unifiedUncached group index.val) input) (data : ProverData Source.BaseField) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.rangeExpression3).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries.get ⟨3, by decide⟩
  have member := ProgramFixedLookup.UnifiedUncached.range_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries ⟨3, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.UnifiedUncached.native.field8_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.range_value3 input.physical data input.arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.UnifiedUncached.native.range16_clean_refinement _ valid _

private theorem range_lookup4
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .unifiedUncached group index.val) input) (data : ProverData Source.BaseField) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.rangeExpression4).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries.get ⟨4, by decide⟩
  have member := ProgramFixedLookup.UnifiedUncached.range_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries ⟨4, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.UnifiedUncached.native.field9_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.range_value4 input.physical data input.arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.UnifiedUncached.native.range16_clean_refinement _ valid _

private theorem range_lookup5
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .unifiedUncached group index.val) input) (data : ProverData Source.BaseField) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.rangeExpression5).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries.get ⟨5, by decide⟩
  have member := ProgramFixedLookup.UnifiedUncached.range_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries ⟨5, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.UnifiedUncached.native.field10_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.range_value5 input.physical data input.arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.UnifiedUncached.native.range16_clean_refinement _ valid _

private theorem range_lookup6
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .unifiedUncached group index.val) input) (data : ProverData Source.BaseField) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.rangeExpression6).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries.get ⟨6, by decide⟩
  have member := ProgramFixedLookup.UnifiedUncached.range_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries ⟨6, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.UnifiedUncached.native.field11_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.range_value6 input.physical data input.arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.UnifiedUncached.native.range16_clean_refinement _ valid _

private theorem range_lookup7
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .unifiedUncached group index.val) input) (data : ProverData Source.BaseField) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.rangeExpression7).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries.get ⟨7, by decide⟩
  have member := ProgramFixedLookup.UnifiedUncached.range_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries ⟨7, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.UnifiedUncached.native.field12_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.range_value7 input.physical data input.arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.UnifiedUncached.native.range16_clean_refinement _ valid _

private theorem range_lookup8
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .unifiedUncached group index.val) input) (data : ProverData Source.BaseField) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.rangeExpression8).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries.get ⟨8, by decide⟩
  have member := ProgramFixedLookup.UnifiedUncached.range_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries ⟨8, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.UnifiedUncached.native.field13_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.range_value8 input.physical data input.arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.UnifiedUncached.native.range16_clean_refinement _ valid _

private theorem range_lookup9
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .unifiedUncached group index.val) input) (data : ProverData Source.BaseField) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.rangeExpression9).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries.get ⟨9, by decide⟩
  have member := ProgramFixedLookup.UnifiedUncached.range_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries ⟨9, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.UnifiedUncached.native.field14_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.range_value9 input.physical data input.arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.UnifiedUncached.native.range16_clean_refinement _ valid _

private theorem range_lookup10
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .unifiedUncached group index.val) input) (data : ProverData Source.BaseField) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.rangeExpression10).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries.get ⟨10, by decide⟩
  have member := ProgramFixedLookup.UnifiedUncached.range_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries ⟨10, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.UnifiedUncached.native.field15_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.range_value10 input.physical data input.arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.UnifiedUncached.native.range16_clean_refinement _ valid _

private theorem range_lookup11
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .unifiedUncached group index.val) input) (data : ProverData Source.BaseField) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.rangeExpression11).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries.get ⟨11, by decide⟩
  have member := ProgramFixedLookup.UnifiedUncached.range_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries ⟨11, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.UnifiedUncached.native.field16_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.range_value11 input.physical data input.arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.UnifiedUncached.native.range16_clean_refinement _ valid _

private theorem range_lookup12
    (decoder : Configuration → List (List Source.BaseField))
    (wordAt : Nat → BitVec 32) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder wordAt .unifiedUncached group index.val) input) (data : ProverData Source.BaseField) :
    (Verification.range16 Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.rangeExpression12).Contains (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries.get ⟨12, by decide⟩
  have member := ProgramFixedLookup.UnifiedUncached.range_from_arguments decoder wordAt input arguments query (List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.range16Queries ⟨12, by decide⟩)
  have nonzero : query.weight (RingHom.id _) ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement) ≠ 0 := by
    change (1 : Source.BaseField) ≠ 0
    exact one_ne_zero
  have valid : Airbender.Compiler.MaterializedNative.UnifiedUncached.native.model.Contains [SourceSetupColumn.range16] [Airbender.Compiler.LookupNative.UnifiedUncached.native.field17_0.source.value ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement)] := member nonzero
  have same := (Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.range_value12 input.physical data input.arithmetic)
  apply clean_scalar_lookup
  rw [same]
  exact Airbender.Compiler.CleanScalarNative.UnifiedUncached.native.range16_clean_refinement _ valid _

private theorem generic_lookup0
    (decoder : Configuration → List (List Source.BaseField))
    (initial : Reference.RiscV.Sail.State) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder
      (Trace.ROM.words initial) .unifiedUncached group index.val) input)
    (guards : ∀ index : Fin 5, (inputRow input).assignment (#v[82, 86, 95, 104, 113][index]) ≠ 46) (data : ProverData Source.BaseField) :
    (Lookup.mk (UnifiedReduced.Setup.table initial).toRaw Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.genericExpressions0).Contains
      (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.genericQueries.get ⟨0, by decide⟩
  obtain ⟨nativeIndex, matched⟩ := source_member_with (fun group index =>
    NativeProgramSetup.rows decoder (Trace.ROM.words initial) .unifiedUncached group index.val) input arguments 0
    (query.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement))
    (List.mem_map.mpr ⟨query, List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.genericQueries ⟨0, by decide⟩, rfl⟩)
    one_ne_zero
  have same0 := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value0_0 input.physical data input.arithmetic
  have same1 := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value0_1 input.physical data input.arithmetic
  have same2 := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value0_2 input.physical data input.arithmetic
  have same3 := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value0_3 input.physical data input.arithmetic
  have same4 := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value0_4 input.physical data input.arithmetic
  have same5 := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value0_5 input.physical data input.arithmetic
  have same6 := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value0_6 input.physical data input.arithmetic
  have same7 := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value0_7 input.physical data input.arithmetic
  have same8 := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value0_8 input.physical data input.arithmetic
  have same9 := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value0_9 input.physical data input.arithmetic
  let actual := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.genericExpressions0.map
    (fun expression => expression.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data))
  have guard : actual[9] ≠ 46 := by
    simp [actual, Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.genericExpressions0,
      Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression0_9, _root_.Expression.eval]
    change (inputRow input).assignment 82 ≠ 46
    exact guards ⟨0, by decide⟩
  apply clean_vector_lookup
  apply NativeProgramSetup.unified_public_member decoder initial .unifiedUncached
    (Or.inl rfl) nativeIndex actual ?_ guard
  simp only [actual, Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.genericExpressions0, Vector.map_mk, List.map_toArray]
  change [(Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression0_0).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression0_1).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression0_2).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression0_3).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression0_4).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression0_5).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression0_6).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression0_7).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression0_8).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression0_9).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data)] = _
  rw [same0, same1, same2, same3, same4, same5, same6, same7, same8, same9]
  exact matched

private theorem generic_lookup1
    (decoder : Configuration → List (List Source.BaseField))
    (initial : Reference.RiscV.Sail.State) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder
      (Trace.ROM.words initial) .unifiedUncached group index.val) input)
    (guards : ∀ index : Fin 5, (inputRow input).assignment (#v[82, 86, 95, 104, 113][index]) ≠ 46) (data : ProverData Source.BaseField) :
    (Lookup.mk (UnifiedReduced.Setup.table initial).toRaw Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.genericExpressions1).Contains
      (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.genericQueries.get ⟨1, by decide⟩
  obtain ⟨nativeIndex, matched⟩ := source_member_with (fun group index =>
    NativeProgramSetup.rows decoder (Trace.ROM.words initial) .unifiedUncached group index.val) input arguments 0
    (query.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement))
    (List.mem_map.mpr ⟨query, List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.genericQueries ⟨1, by decide⟩, rfl⟩)
    one_ne_zero
  have same0 := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value1_0 input.physical data input.arithmetic
  have same1 := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value1_1 input.physical data input.arithmetic
  have same2 := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value1_2 input.physical data input.arithmetic
  have same3 := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value1_3 input.physical data input.arithmetic
  have same4 := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value1_4 input.physical data input.arithmetic
  have same5 := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value1_5 input.physical data input.arithmetic
  have same6 := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value1_6 input.physical data input.arithmetic
  have same7 := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value1_7 input.physical data input.arithmetic
  have same8 := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value1_8 input.physical data input.arithmetic
  have same9 := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value1_9 input.physical data input.arithmetic
  let actual := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.genericExpressions1.map
    (fun expression => expression.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data))
  have guard : actual[9] ≠ 46 := by
    simp [actual, Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.genericExpressions1,
      Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression1_9, _root_.Expression.eval]
    change (inputRow input).assignment 86 ≠ 46
    exact guards ⟨1, by decide⟩
  apply clean_vector_lookup
  apply NativeProgramSetup.unified_public_member decoder initial .unifiedUncached
    (Or.inl rfl) nativeIndex actual ?_ guard
  simp only [actual, Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.genericExpressions1, Vector.map_mk, List.map_toArray]
  change [(Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression1_0).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression1_1).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression1_2).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression1_3).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression1_4).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression1_5).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression1_6).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression1_7).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression1_8).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression1_9).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data)] = _
  rw [same0, same1, same2, same3, same4, same5, same6, same7, same8, same9]
  exact matched

private theorem generic_lookup2
    (decoder : Configuration → List (List Source.BaseField))
    (initial : Reference.RiscV.Sail.State) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder
      (Trace.ROM.words initial) .unifiedUncached group index.val) input)
    (guards : ∀ index : Fin 5, (inputRow input).assignment (#v[82, 86, 95, 104, 113][index]) ≠ 46) (data : ProverData Source.BaseField) :
    (Lookup.mk (UnifiedReduced.Setup.table initial).toRaw Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.genericExpressions2).Contains
      (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.genericQueries.get ⟨2, by decide⟩
  obtain ⟨nativeIndex, matched⟩ := source_member_with (fun group index =>
    NativeProgramSetup.rows decoder (Trace.ROM.words initial) .unifiedUncached group index.val) input arguments 0
    (query.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement))
    (List.mem_map.mpr ⟨query, List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.genericQueries ⟨2, by decide⟩, rfl⟩)
    one_ne_zero
  have same0 := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value2_0 input.physical data input.arithmetic
  have same1 := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value2_1 input.physical data input.arithmetic
  have same2 := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value2_2 input.physical data input.arithmetic
  have same3 := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value2_3 input.physical data input.arithmetic
  have same4 := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value2_4 input.physical data input.arithmetic
  have same5 := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value2_5 input.physical data input.arithmetic
  have same6 := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value2_6 input.physical data input.arithmetic
  have same7 := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value2_7 input.physical data input.arithmetic
  have same8 := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value2_8 input.physical data input.arithmetic
  have same9 := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value2_9 input.physical data input.arithmetic
  let actual := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.genericExpressions2.map
    (fun expression => expression.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data))
  have guard : actual[9] ≠ 46 := by
    simp [actual, Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.genericExpressions2,
      Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression2_9, _root_.Expression.eval]
    change (inputRow input).assignment 95 ≠ 46
    exact guards ⟨2, by decide⟩
  apply clean_vector_lookup
  apply NativeProgramSetup.unified_public_member decoder initial .unifiedUncached
    (Or.inl rfl) nativeIndex actual ?_ guard
  simp only [actual, Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.genericExpressions2, Vector.map_mk, List.map_toArray]
  change [(Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression2_0).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression2_1).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression2_2).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression2_3).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression2_4).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression2_5).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression2_6).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression2_7).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression2_8).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression2_9).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data)] = _
  rw [same0, same1, same2, same3, same4, same5, same6, same7, same8, same9]
  exact matched

private theorem generic_lookup3
    (decoder : Configuration → List (List Source.BaseField))
    (initial : Reference.RiscV.Sail.State) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder
      (Trace.ROM.words initial) .unifiedUncached group index.val) input)
    (guards : ∀ index : Fin 5, (inputRow input).assignment (#v[82, 86, 95, 104, 113][index]) ≠ 46) (data : ProverData Source.BaseField) :
    (Lookup.mk (UnifiedReduced.Setup.table initial).toRaw Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.genericExpressions3).Contains
      (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.genericQueries.get ⟨3, by decide⟩
  obtain ⟨nativeIndex, matched⟩ := source_member_with (fun group index =>
    NativeProgramSetup.rows decoder (Trace.ROM.words initial) .unifiedUncached group index.val) input arguments 0
    (query.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement))
    (List.mem_map.mpr ⟨query, List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.genericQueries ⟨3, by decide⟩, rfl⟩)
    one_ne_zero
  have same0 := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value3_0 input.physical data input.arithmetic
  have same1 := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value3_1 input.physical data input.arithmetic
  have same2 := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value3_2 input.physical data input.arithmetic
  have same3 := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value3_3 input.physical data input.arithmetic
  have same4 := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value3_4 input.physical data input.arithmetic
  have same5 := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value3_5 input.physical data input.arithmetic
  have same6 := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value3_6 input.physical data input.arithmetic
  have same7 := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value3_7 input.physical data input.arithmetic
  have same8 := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value3_8 input.physical data input.arithmetic
  have same9 := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value3_9 input.physical data input.arithmetic
  let actual := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.genericExpressions3.map
    (fun expression => expression.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data))
  have guard : actual[9] ≠ 46 := by
    simp [actual, Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.genericExpressions3,
      Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression3_9, _root_.Expression.eval]
    change (inputRow input).assignment 104 ≠ 46
    exact guards ⟨3, by decide⟩
  apply clean_vector_lookup
  apply NativeProgramSetup.unified_public_member decoder initial .unifiedUncached
    (Or.inl rfl) nativeIndex actual ?_ guard
  simp only [actual, Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.genericExpressions3, Vector.map_mk, List.map_toArray]
  change [(Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression3_0).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression3_1).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression3_2).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression3_3).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression3_4).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression3_5).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression3_6).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression3_7).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression3_8).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression3_9).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data)] = _
  rw [same0, same1, same2, same3, same4, same5, same6, same7, same8, same9]
  exact matched

private theorem generic_lookup4
    (decoder : Configuration → List (List Source.BaseField))
    (initial : Reference.RiscV.Sail.State) (input : Input)
    (arguments : LookupArgumentsWith (fun group index => NativeProgramSetup.rows decoder
      (Trace.ROM.words initial) .unifiedUncached group index.val) input)
    (guards : ∀ index : Fin 5, (inputRow input).assignment (#v[82, 86, 95, 104, 113][index]) ≠ 46) (data : ProverData Source.BaseField) :
    (Lookup.mk (UnifiedReduced.Setup.table initial).toRaw Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.genericExpressions4).Contains
      (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data) := by
  let query := Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.genericQueries.get ⟨4, by decide⟩
  obtain ⟨nativeIndex, matched⟩ := source_member_with (fun group index =>
    NativeProgramSetup.rows decoder (Trace.ROM.words initial) .unifiedUncached group index.val) input arguments 0
    (query.materialized ((input.physical ∘ Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.bank.address) ∘ Airbender.Compiler.LookupNative.UnifiedUncached.native.sourcePlacement))
    (List.mem_map.mpr ⟨query, List.get_mem Airbender.Compiler.LookupSourceNative.UnifiedUncached.native.genericQueries ⟨4, by decide⟩, rfl⟩)
    one_ne_zero
  have same0 := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value4_0 input.physical data input.arithmetic
  have same1 := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value4_1 input.physical data input.arithmetic
  have same2 := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value4_2 input.physical data input.arithmetic
  have same3 := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value4_3 input.physical data input.arithmetic
  have same4 := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value4_4 input.physical data input.arithmetic
  have same5 := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value4_5 input.physical data input.arithmetic
  have same6 := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value4_6 input.physical data input.arithmetic
  have same7 := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value4_7 input.physical data input.arithmetic
  have same8 := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value4_8 input.physical data input.arithmetic
  have same9 := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.generic_value4_9 input.physical data input.arithmetic
  let actual := Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.genericExpressions4.map
    (fun expression => expression.eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data))
  have guard : actual[9] ≠ 46 := by
    simp [actual, Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.genericExpressions4,
      Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression4_9, _root_.Expression.eval]
    change (inputRow input).assignment 113 ≠ 46
    exact guards ⟨4, by decide⟩
  apply clean_vector_lookup
  apply NativeProgramSetup.unified_public_member decoder initial .unifiedUncached
    (Or.inl rfl) nativeIndex actual ?_ guard
  simp only [actual, Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.genericExpressions4, Vector.map_mk, List.map_toArray]
  change [(Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression4_0).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression4_1).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression4_2).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression4_3).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression4_4).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression4_5).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression4_6).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression4_7).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression4_8).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data), (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.part0.genericExpression4_9).eval (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical data)] = _
  rw [same0, same1, same2, same3, same4, same5, same6, same7, same8, same9]
  exact matched

private theorem clock_lookup_inventory (setup : Table Source.BaseField (fields 10)) :
    FlatOperation.lookups (Airbender.UnifiedReduced.clockConstraints (p := babyBearModulus) setup) =
    (Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.rangeExpressions.map Verification.range16) ++
    (Airbender.Compiler.CleanGenericArgumentsNative.UnifiedUncached.native.genericExpressions.map (fun entry => Lookup.mk setup.toRaw entry)) ++
    (Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.timestampExpressions.map Trace.timestampLookup) := by rfl

/-- Public decoding and exact native matching prove all unified row constraints. -/
theorem input_constraints
    {initial : Reference.RiscV.Sail.State} {text : List (BitVec 32)} {capacity : Nat}
    {mask : Trace.NativeDecoder.ProgramRows.Mask} {columns : List (List Source.BaseField)}
    (setup : UnifiedProgramSetup initial text capacity mask columns)
    (input : Input)
    (arguments : LookupArgumentsWith (fun group index =>
      NativeProgramSetup.unifiedLookupRows initial columns .unifiedUncached group index.val) input)
    (typed : (inputRow input).decoderQuery[0].val < 65536) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment (inputRow input).assignment)
      ((inputRow input).constraints (UnifiedReduced.Setup.table initial)) := by
  have helpers := ProgramFixedLookup.UnifiedUncached.helpers_from_arguments
    (NativeProgramSetup.unifiedDecoderColumns columns) (Trace.ROM.words initial) input arguments
  have assertions : ∀ expression ∈ FlatOperation.constraints (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table initial)),
      expression.eval (Verification.environment (inputRow input).assignment) = 0 := by
    rw [Airbender.Compiler.CleanLinksNative.UnifiedUncached.arithmetic_inventory]
    exact CleanExpression.assertions_only _ _
      (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.arithmetic_preserved input.physical (fun _ _ => #[]) input.arithmetic)
  have matched := ProgramDecoderLookup.UnifiedUncached.decoder_lookup setup input arguments typed
  have operation := public_unified_operation setup (inputRow input).assignment matched typed
  have guards := UnifiedPublicConstraints.helper_not_decoder _ (inputRow input).assignment assertions input.active operation
  apply Airbender.Compiler.CleanLinksNative.UnifiedUncached.retained_clock_constraints (UnifiedReduced.Setup.table initial) input.physical (fun _ _ => #[]) input.arithmetic
  rw [clock_lookup_inventory]
  exact PredicateChecks.all (PredicateChecks.cons (range_lookup0 (NativeProgramSetup.unifiedDecoderColumns columns) (Trace.ROM.words initial) input arguments (fun _ _ => #[])) (PredicateChecks.cons (range_lookup1 (NativeProgramSetup.unifiedDecoderColumns columns) (Trace.ROM.words initial) input arguments (fun _ _ => #[])) (PredicateChecks.cons (range_lookup2 (NativeProgramSetup.unifiedDecoderColumns columns) (Trace.ROM.words initial) input arguments (fun _ _ => #[])) (PredicateChecks.cons (range_lookup3 (NativeProgramSetup.unifiedDecoderColumns columns) (Trace.ROM.words initial) input arguments (fun _ _ => #[])) (PredicateChecks.cons (range_lookup4 (NativeProgramSetup.unifiedDecoderColumns columns) (Trace.ROM.words initial) input arguments (fun _ _ => #[])) (PredicateChecks.cons (range_lookup5 (NativeProgramSetup.unifiedDecoderColumns columns) (Trace.ROM.words initial) input arguments (fun _ _ => #[])) (PredicateChecks.cons (range_lookup6 (NativeProgramSetup.unifiedDecoderColumns columns) (Trace.ROM.words initial) input arguments (fun _ _ => #[])) (PredicateChecks.cons (range_lookup7 (NativeProgramSetup.unifiedDecoderColumns columns) (Trace.ROM.words initial) input arguments (fun _ _ => #[])) (PredicateChecks.cons (range_lookup8 (NativeProgramSetup.unifiedDecoderColumns columns) (Trace.ROM.words initial) input arguments (fun _ _ => #[])) (PredicateChecks.cons (range_lookup9 (NativeProgramSetup.unifiedDecoderColumns columns) (Trace.ROM.words initial) input arguments (fun _ _ => #[])) (PredicateChecks.cons (range_lookup10 (NativeProgramSetup.unifiedDecoderColumns columns) (Trace.ROM.words initial) input arguments (fun _ _ => #[])) (PredicateChecks.cons (range_lookup11 (NativeProgramSetup.unifiedDecoderColumns columns) (Trace.ROM.words initial) input arguments (fun _ _ => #[])) (PredicateChecks.cons (range_lookup12 (NativeProgramSetup.unifiedDecoderColumns columns) (Trace.ROM.words initial) input arguments (fun _ _ => #[])) (PredicateChecks.cons (generic_lookup0 (NativeProgramSetup.unifiedDecoderColumns columns) initial input arguments guards (fun _ _ => #[])) (PredicateChecks.cons (generic_lookup1 (NativeProgramSetup.unifiedDecoderColumns columns) initial input arguments guards (fun _ _ => #[])) (PredicateChecks.cons (generic_lookup2 (NativeProgramSetup.unifiedDecoderColumns columns) initial input arguments guards (fun _ _ => #[])) (PredicateChecks.cons (generic_lookup3 (NativeProgramSetup.unifiedDecoderColumns columns) initial input arguments guards (fun _ _ => #[])) (PredicateChecks.cons (generic_lookup4 (NativeProgramSetup.unifiedDecoderColumns columns) initial input arguments guards (fun _ _ => #[])) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.timestampExpression0 (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.timestamp_bound0 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.timestampExpression1 (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.timestamp_bound1 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.timestampExpression2 (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.timestamp_bound2 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.timestampExpression3 (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.timestamp_bound3 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.timestampExpression4 (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.timestamp_bound4 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.timestampExpression5 (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.timestamp_bound5 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.timestampExpression6 (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.timestamp_bound6 input.physical (fun _ _ => #[]) input.arithmetic helpers)) (PredicateChecks.cons (clean_timestamp_lookup Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.timestampExpression7 (Airbender.Compiler.CleanArithmeticNative.UnifiedUncached.native.environment input.physical (fun _ _ => #[])) (Airbender.Compiler.CleanArgumentsNative.UnifiedUncached.native.timestamp_bound7 input.physical (fun _ _ => #[]) input.arithmetic helpers)) PredicateChecks.nil))))))))))))))))))))))))))

end Airbender.Compiler.ProgramConstraintsNative.UnifiedUncached
