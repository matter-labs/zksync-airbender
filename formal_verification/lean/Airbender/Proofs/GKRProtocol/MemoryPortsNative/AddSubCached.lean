import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.AddSubCached
import Airbender.Proofs.GKRProtocol.MemoryTokens
import Airbender.Proofs.GKRProtocol.MemoryNative.AddSubCached
import Airbender.Proofs.GKRProtocol.FunctionalLinksNative.AddSubCached
import Airbender.Proofs.GKRProtocol.NativeWitness
import Airbender.Review.Circuits.AddSub.Artifact

namespace Airbender.Compiler.MemoryPortsNative.AddSubCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem source_read_tokens (assignment : Nat → Source.BaseField) (other : Source.MemoryValues) :
    (Airbender.Compiler.MemoryNative.AddSubCached.native.memoryReadRows.map (fun row => row.token {other with original := assignment})) =
      Airbender.AddSub.importedConstraintsMemoryPorts.toList.map (Trace.readToken assignment) ++
        [pcStateMemoryToken ⟨Trace.rawPair assignment Airbender.AddSub.importedConstraintsTraceColumns.initialPC,
          Trace.rawPair assignment Airbender.AddSub.importedConstraintsTraceColumns.initialTime⟩] := by
  rfl

theorem source_write_tokens (assignment : Nat → Source.BaseField) (other : Source.MemoryValues) :
    (Airbender.Compiler.MemoryNative.AddSubCached.native.memoryWriteRows.map (fun row => row.token {other with original := assignment})) =
      Airbender.AddSub.importedConstraintsMemoryPorts.toList.map (Trace.writeToken Airbender.AddSub.importedConstraintsTraceColumns assignment) ++
        [pcStateMemoryToken ⟨Trace.rawPair assignment Airbender.AddSub.importedConstraintsTraceColumns.finalPC,
          Trace.rawPair assignment Airbender.AddSub.importedConstraintsTraceColumns.finalTime⟩] := by
  rfl

theorem original_columns : (List.range 42).all (fun index =>
    decide (Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement index) =
      Airbender.Compiler.MemoryNative.AddSubCached.native.bank.address (Airbender.Compiler.MemoryNative.AddSubCached.native.sourcePlacement.original index))) = true := by decide +kernel

theorem original_assignment (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (index : Nat) (bounded : index < 42) :
    (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data).get index = (Airbender.Compiler.MemoryNative.AddSubCached.native.sourceValues physical).original index := by
  exact congrArg physical (of_decide_eq_true (List.all_eq_true.mp original_columns index (List.mem_range.mpr bounded)))

theorem read_original_indices : Airbender.Compiler.MemoryNative.AddSubCached.native.memoryReadRows.all
    (fun row => row.originalIndices.all (fun index => decide (index < 42))) = true := by decide +kernel

theorem read_tokens_from_base (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField) :
    Airbender.Compiler.MemoryNative.AddSubCached.native.memoryReadRows.map (fun row => row.token (Airbender.Compiler.MemoryNative.AddSubCached.native.sourceValues physical)) =
      Airbender.AddSub.importedConstraintsMemoryPorts.toList.map (Trace.readToken (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data).get) ++
        [pcStateMemoryToken ⟨Trace.rawPair (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data).get Airbender.AddSub.importedConstraintsTraceColumns.initialPC,
          Trace.rawPair (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data).get Airbender.AddSub.importedConstraintsTraceColumns.initialTime⟩] := by
  rw [← source_read_tokens (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data).get (Airbender.Compiler.MemoryNative.AddSubCached.native.sourceValues physical)]
  apply List.map_congr_left
  intro row member
  apply Source.MemoryRow.token_congr
  intro field included
  apply Eq.symm
  apply Source.MemoryField.withOriginal_value
  intro index used
  apply original_assignment
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp read_original_indices row member) index
    (List.mem_flatMap.mpr ⟨field, included, used⟩))

theorem write_original_indices : Airbender.Compiler.MemoryNative.AddSubCached.native.memoryWriteRows.all
    (fun row => row.originalIndices.all (fun index => decide (index < 42))) = true := by decide +kernel

theorem write_tokens_from_base (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField) :
    Airbender.Compiler.MemoryNative.AddSubCached.native.memoryWriteRows.map (fun row => row.token (Airbender.Compiler.MemoryNative.AddSubCached.native.sourceValues physical)) =
      Airbender.AddSub.importedConstraintsMemoryPorts.toList.map (Trace.writeToken Airbender.AddSub.importedConstraintsTraceColumns (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data).get) ++
        [pcStateMemoryToken ⟨Trace.rawPair (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data).get Airbender.AddSub.importedConstraintsTraceColumns.finalPC,
          Trace.rawPair (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data).get Airbender.AddSub.importedConstraintsTraceColumns.finalTime⟩] := by
  rw [← source_write_tokens (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data).get (Airbender.Compiler.MemoryNative.AddSubCached.native.sourceValues physical)]
  apply List.map_congr_left
  intro row member
  apply Source.MemoryRow.token_congr
  intro field included
  apply Eq.symm
  apply Source.MemoryField.withOriginal_value
  intro index used
  apply original_assignment
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp write_original_indices row member) index
    (List.mem_flatMap.mpr ⟨field, included, used⟩))

theorem read_products_from_base {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField) :
    (Airbender.Compiler.MemoryNative.AddSubCached.native.memoryReadRows.map (fun row => row.fingerprint (Airbender.Compiler.MemoryNative.AddSubCached.native.sourceValues physical) hom challenges)).prod =
      ((Airbender.AddSub.importedConstraintsMemoryPorts.toList.map (Trace.readToken (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data).get) ++
        [pcStateMemoryToken ⟨Trace.rawPair (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data).get Airbender.AddSub.importedConstraintsTraceColumns.initialPC,
          Trace.rawPair (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data).get Airbender.AddSub.importedConstraintsTraceColumns.initialTime⟩]).map
        (memoryTokenFingerprint hom challenges)).prod := by
  rw [← Source.MemoryRow.token_products Airbender.Compiler.MemoryNative.AddSubCached.native.memoryReadRows (Airbender.Compiler.MemoryNative.AddSubCached.native.sourceValues physical) hom challenges,
    read_tokens_from_base physical data]

theorem write_products_from_base {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField) :
    (Airbender.Compiler.MemoryNative.AddSubCached.native.memoryWriteRows.map (fun row => row.fingerprint (Airbender.Compiler.MemoryNative.AddSubCached.native.sourceValues physical) hom challenges)).prod =
      ((Airbender.AddSub.importedConstraintsMemoryPorts.toList.map (Trace.writeToken Airbender.AddSub.importedConstraintsTraceColumns (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data).get) ++
        [pcStateMemoryToken ⟨Trace.rawPair (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data).get Airbender.AddSub.importedConstraintsTraceColumns.finalPC,
          Trace.rawPair (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data).get Airbender.AddSub.importedConstraintsTraceColumns.finalTime⟩]).map
        (memoryTokenFingerprint hom challenges)).prod := by
  rw [← Source.MemoryRow.token_products Airbender.Compiler.MemoryNative.AddSubCached.native.memoryWriteRows (Airbender.Compiler.MemoryNative.AddSubCached.native.sourceValues physical) hom challenges,
    write_tokens_from_base physical data]

theorem read_output_logical {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (values : GKRAddress → R)
    (baseLaw : ∀ address, Airbender.Compiler.FunctionalNative.AddSubCached.native.isBase address = true → values address = hom (physical address))
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0)
    (affine : ∀ definition ∈ Airbender.Compiler.FunctionalNative.AddSubCached.native.definitions, definition.Holds hom challenges values)
    (products : ∀ gate ∈ Airbender.Compiler.ProductNative.AddSubCached.native.gates, gate.Holds hom challenges values) :
    values Airbender.Compiler.MemoryNative.AddSubCached.native.memoryReadOutput =
      maskProduct (hom ((Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data).get Airbender.AddSub.importedConstraintsTraceColumns.execute))
      ((Airbender.AddSub.importedConstraintsMemoryPorts.toList.map (Trace.readToken (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data).get) ++
        [pcStateMemoryToken ⟨Trace.rawPair (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data).get Airbender.AddSub.importedConstraintsTraceColumns.initialPC,
          Trace.rawPair (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data).get Airbender.AddSub.importedConstraintsTraceColumns.initialTime⟩]).map
        (memoryTokenFingerprint hom challenges)).prod := by
  let assignment : TypedAssignment R := ⟨physical, values⟩
  have typedEq : assignment.value Airbender.Compiler.ConsumerNative.AddSubCached.native.typing hom = values := TypedAssignment.value_eq assignment Airbender.Compiler.ConsumerNative.AddSubCached.native.typing hom baseLaw
  have defined : ∀ definition ∈ Airbender.Compiler.MemoryNative.AddSubCached.native.definitions, definition.Holds hom challenges (assignment.value Airbender.Compiler.ConsumerNative.AddSubCached.native.typing hom) := by
    rw [typedEq, ← Airbender.Compiler.FunctionalLinksNative.AddSubCached.native.memoryDefinitionsAgree]
    exact affine
  have holds := products
  rw [← typedEq] at holds
  have reduced := Airbender.Compiler.MemoryNative.AddSubCached.native.memoryReadSourceReduction hom challenges assignment defined (Airbender.Compiler.FunctionalLinksNative.AddSubCached.native.memoryCopies physical arithmetic) holds
  rw [typedEq] at reduced
  change values Airbender.Compiler.MemoryNative.AddSubCached.native.memoryReadOutput = maskProduct (hom (Airbender.Compiler.MemoryNative.AddSubCached.native.sourceExecute.value (Airbender.Compiler.MemoryNative.AddSubCached.native.sourceValues physical)))
    (Airbender.Compiler.MemoryNative.AddSubCached.native.memoryReadRows.map (fun row => row.fingerprint (Airbender.Compiler.MemoryNative.AddSubCached.native.sourceValues physical) hom challenges)).prod at reduced
  have executeSame : Airbender.Compiler.MemoryNative.AddSubCached.native.sourceExecute.value (Airbender.Compiler.MemoryNative.AddSubCached.native.sourceValues physical) =
      (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data).get Airbender.AddSub.importedConstraintsTraceColumns.execute :=
    (original_assignment physical data 4 (by decide +kernel)).symm
  rw [executeSame, read_products_from_base hom challenges physical data] at reduced
  exact reduced

theorem write_output_logical {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (values : GKRAddress → R)
    (baseLaw : ∀ address, Airbender.Compiler.FunctionalNative.AddSubCached.native.isBase address = true → values address = hom (physical address))
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank.address) = 0)
    (affine : ∀ definition ∈ Airbender.Compiler.FunctionalNative.AddSubCached.native.definitions, definition.Holds hom challenges values)
    (products : ∀ gate ∈ Airbender.Compiler.ProductNative.AddSubCached.native.gates, gate.Holds hom challenges values) :
    values Airbender.Compiler.MemoryNative.AddSubCached.native.memoryWriteOutput =
      maskProduct (hom ((Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data).get Airbender.AddSub.importedConstraintsTraceColumns.execute))
      ((Airbender.AddSub.importedConstraintsMemoryPorts.toList.map (Trace.writeToken Airbender.AddSub.importedConstraintsTraceColumns (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data).get) ++
        [pcStateMemoryToken ⟨Trace.rawPair (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data).get Airbender.AddSub.importedConstraintsTraceColumns.finalPC,
          Trace.rawPair (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data).get Airbender.AddSub.importedConstraintsTraceColumns.finalTime⟩]).map
        (memoryTokenFingerprint hom challenges)).prod := by
  let assignment : TypedAssignment R := ⟨physical, values⟩
  have typedEq : assignment.value Airbender.Compiler.ConsumerNative.AddSubCached.native.typing hom = values := TypedAssignment.value_eq assignment Airbender.Compiler.ConsumerNative.AddSubCached.native.typing hom baseLaw
  have defined : ∀ definition ∈ Airbender.Compiler.MemoryNative.AddSubCached.native.definitions, definition.Holds hom challenges (assignment.value Airbender.Compiler.ConsumerNative.AddSubCached.native.typing hom) := by
    rw [typedEq, ← Airbender.Compiler.FunctionalLinksNative.AddSubCached.native.memoryDefinitionsAgree]
    exact affine
  have holds := products
  rw [← typedEq] at holds
  have reduced := Airbender.Compiler.MemoryNative.AddSubCached.native.memoryWriteSourceReduction hom challenges assignment defined (Airbender.Compiler.FunctionalLinksNative.AddSubCached.native.memoryCopies physical arithmetic) holds
  rw [typedEq] at reduced
  change values Airbender.Compiler.MemoryNative.AddSubCached.native.memoryWriteOutput = maskProduct (hom (Airbender.Compiler.MemoryNative.AddSubCached.native.sourceExecute.value (Airbender.Compiler.MemoryNative.AddSubCached.native.sourceValues physical)))
    (Airbender.Compiler.MemoryNative.AddSubCached.native.memoryWriteRows.map (fun row => row.fingerprint (Airbender.Compiler.MemoryNative.AddSubCached.native.sourceValues physical) hom challenges)).prod at reduced
  have executeSame : Airbender.Compiler.MemoryNative.AddSubCached.native.sourceExecute.value (Airbender.Compiler.MemoryNative.AddSubCached.native.sourceValues physical) =
      (Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.environment physical data).get Airbender.AddSub.importedConstraintsTraceColumns.execute :=
    (original_assignment physical data 4 (by decide +kernel)).symm
  rw [executeSame, write_products_from_base hom challenges physical data] at reduced
  exact reduced

end Airbender.Compiler.MemoryPortsNative.AddSubCached
