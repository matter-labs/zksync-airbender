import GKRProtocol.CleanArithmeticNative.MulDivCached
import GKRProtocol.MemoryTokens
import GKRProtocol.MemoryNative.MulDivCached
import GKRProtocol.FunctionalLinksNative.MulDivCached
import GKRProtocol.NativeWitness
import Airbender.Review.Circuits.MulDiv.Artifact

namespace Airbender.Compiler.MemoryPortsNative.MulDivCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem source_read_tokens (assignment : Nat → Source.BaseField) (other : Source.MemoryValues) :
    (Airbender.Compiler.MemoryNative.MulDivCached.native.memoryReadRows.map (fun row => row.token {other with original := assignment})) =
      Airbender.MulDiv.importedConstraintsMemoryPorts.toList.map (Trace.readToken assignment) ++
        [pcStateMemoryToken ⟨Trace.rawPair assignment Airbender.MulDiv.importedConstraintsTraceColumns.initialPC,
          Trace.rawPair assignment Airbender.MulDiv.importedConstraintsTraceColumns.initialTime⟩] := by
  rfl

theorem source_write_tokens (assignment : Nat → Source.BaseField) (other : Source.MemoryValues) :
    (Airbender.Compiler.MemoryNative.MulDivCached.native.memoryWriteRows.map (fun row => row.token {other with original := assignment})) =
      Airbender.MulDiv.importedConstraintsMemoryPorts.toList.map (Trace.writeToken Airbender.MulDiv.importedConstraintsTraceColumns assignment) ++
        [pcStateMemoryToken ⟨Trace.rawPair assignment Airbender.MulDiv.importedConstraintsTraceColumns.finalPC,
          Trace.rawPair assignment Airbender.MulDiv.importedConstraintsTraceColumns.finalTime⟩] := by
  rfl

theorem original_columns : (List.range 65).all (fun index =>
    decide (Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.placement index) =
      Airbender.Compiler.MemoryNative.MulDivCached.native.bank.address (Airbender.Compiler.MemoryNative.MulDivCached.native.sourcePlacement.original index))) = true := by decide +kernel

theorem original_assignment (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (index : Nat) (bounded : index < 65) :
    (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data).get index = (Airbender.Compiler.MemoryNative.MulDivCached.native.sourceValues physical).original index := by
  exact congrArg physical (of_decide_eq_true (List.all_eq_true.mp original_columns index (List.mem_range.mpr bounded)))

theorem read_original_indices : Airbender.Compiler.MemoryNative.MulDivCached.native.memoryReadRows.all
    (fun row => row.originalIndices.all (fun index => decide (index < 65))) = true := by decide +kernel

theorem read_tokens_from_base (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField) :
    Airbender.Compiler.MemoryNative.MulDivCached.native.memoryReadRows.map (fun row => row.token (Airbender.Compiler.MemoryNative.MulDivCached.native.sourceValues physical)) =
      Airbender.MulDiv.importedConstraintsMemoryPorts.toList.map (Trace.readToken (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data).get) ++
        [pcStateMemoryToken ⟨Trace.rawPair (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data).get Airbender.MulDiv.importedConstraintsTraceColumns.initialPC,
          Trace.rawPair (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data).get Airbender.MulDiv.importedConstraintsTraceColumns.initialTime⟩] := by
  rw [← source_read_tokens (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data).get (Airbender.Compiler.MemoryNative.MulDivCached.native.sourceValues physical)]
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

theorem write_original_indices : Airbender.Compiler.MemoryNative.MulDivCached.native.memoryWriteRows.all
    (fun row => row.originalIndices.all (fun index => decide (index < 65))) = true := by decide +kernel

theorem write_tokens_from_base (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField) :
    Airbender.Compiler.MemoryNative.MulDivCached.native.memoryWriteRows.map (fun row => row.token (Airbender.Compiler.MemoryNative.MulDivCached.native.sourceValues physical)) =
      Airbender.MulDiv.importedConstraintsMemoryPorts.toList.map (Trace.writeToken Airbender.MulDiv.importedConstraintsTraceColumns (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data).get) ++
        [pcStateMemoryToken ⟨Trace.rawPair (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data).get Airbender.MulDiv.importedConstraintsTraceColumns.finalPC,
          Trace.rawPair (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data).get Airbender.MulDiv.importedConstraintsTraceColumns.finalTime⟩] := by
  rw [← source_write_tokens (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data).get (Airbender.Compiler.MemoryNative.MulDivCached.native.sourceValues physical)]
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
    (Airbender.Compiler.MemoryNative.MulDivCached.native.memoryReadRows.map (fun row => row.fingerprint (Airbender.Compiler.MemoryNative.MulDivCached.native.sourceValues physical) hom challenges)).prod =
      ((Airbender.MulDiv.importedConstraintsMemoryPorts.toList.map (Trace.readToken (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data).get) ++
        [pcStateMemoryToken ⟨Trace.rawPair (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data).get Airbender.MulDiv.importedConstraintsTraceColumns.initialPC,
          Trace.rawPair (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data).get Airbender.MulDiv.importedConstraintsTraceColumns.initialTime⟩]).map
        (memoryTokenFingerprint hom challenges)).prod := by
  rw [← Source.MemoryRow.token_products Airbender.Compiler.MemoryNative.MulDivCached.native.memoryReadRows (Airbender.Compiler.MemoryNative.MulDivCached.native.sourceValues physical) hom challenges,
    read_tokens_from_base physical data]

theorem write_products_from_base {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField) :
    (Airbender.Compiler.MemoryNative.MulDivCached.native.memoryWriteRows.map (fun row => row.fingerprint (Airbender.Compiler.MemoryNative.MulDivCached.native.sourceValues physical) hom challenges)).prod =
      ((Airbender.MulDiv.importedConstraintsMemoryPorts.toList.map (Trace.writeToken Airbender.MulDiv.importedConstraintsTraceColumns (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data).get) ++
        [pcStateMemoryToken ⟨Trace.rawPair (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data).get Airbender.MulDiv.importedConstraintsTraceColumns.finalPC,
          Trace.rawPair (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data).get Airbender.MulDiv.importedConstraintsTraceColumns.finalTime⟩]).map
        (memoryTokenFingerprint hom challenges)).prod := by
  rw [← Source.MemoryRow.token_products Airbender.Compiler.MemoryNative.MulDivCached.native.memoryWriteRows (Airbender.Compiler.MemoryNative.MulDivCached.native.sourceValues physical) hom challenges,
    write_tokens_from_base physical data]

theorem read_output_logical {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (values : GKRAddress → R)
    (baseLaw : ∀ address, Airbender.Compiler.FunctionalNative.MulDivCached.native.isBase address = true → values address = hom (physical address))
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0)
    (affine : ∀ definition ∈ Airbender.Compiler.FunctionalNative.MulDivCached.native.definitions, definition.Holds hom challenges values)
    (products : ∀ gate ∈ Airbender.Compiler.ProductNative.MulDivCached.native.gates, gate.Holds hom challenges values) :
    values Airbender.Compiler.MemoryNative.MulDivCached.native.memoryReadOutput =
      maskProduct (hom ((Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data).get Airbender.MulDiv.importedConstraintsTraceColumns.execute))
      ((Airbender.MulDiv.importedConstraintsMemoryPorts.toList.map (Trace.readToken (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data).get) ++
        [pcStateMemoryToken ⟨Trace.rawPair (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data).get Airbender.MulDiv.importedConstraintsTraceColumns.initialPC,
          Trace.rawPair (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data).get Airbender.MulDiv.importedConstraintsTraceColumns.initialTime⟩]).map
        (memoryTokenFingerprint hom challenges)).prod := by
  let assignment : TypedAssignment R := ⟨physical, values⟩
  have typedEq : assignment.value Airbender.Compiler.ConsumerNative.MulDivCached.native.typing hom = values := TypedAssignment.value_eq assignment Airbender.Compiler.ConsumerNative.MulDivCached.native.typing hom baseLaw
  have defined : ∀ definition ∈ Airbender.Compiler.MemoryNative.MulDivCached.native.definitions, definition.Holds hom challenges (assignment.value Airbender.Compiler.ConsumerNative.MulDivCached.native.typing hom) := by
    rw [typedEq, ← Airbender.Compiler.FunctionalLinksNative.MulDivCached.native.memoryDefinitionsAgree]
    exact affine
  have holds := products
  rw [← typedEq] at holds
  have reduced := Airbender.Compiler.MemoryNative.MulDivCached.native.memoryReadSourceReduction hom challenges assignment defined (Airbender.Compiler.FunctionalLinksNative.MulDivCached.native.memoryCopies physical arithmetic) holds
  rw [typedEq] at reduced
  change values Airbender.Compiler.MemoryNative.MulDivCached.native.memoryReadOutput = maskProduct (hom (Airbender.Compiler.MemoryNative.MulDivCached.native.sourceExecute.value (Airbender.Compiler.MemoryNative.MulDivCached.native.sourceValues physical)))
    (Airbender.Compiler.MemoryNative.MulDivCached.native.memoryReadRows.map (fun row => row.fingerprint (Airbender.Compiler.MemoryNative.MulDivCached.native.sourceValues physical) hom challenges)).prod at reduced
  have executeSame : Airbender.Compiler.MemoryNative.MulDivCached.native.sourceExecute.value (Airbender.Compiler.MemoryNative.MulDivCached.native.sourceValues physical) =
      (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data).get Airbender.MulDiv.importedConstraintsTraceColumns.execute :=
    (original_assignment physical data 4 (by decide +kernel)).symm
  rw [executeSame, read_products_from_base hom challenges physical data] at reduced
  exact reduced

theorem write_output_logical {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (values : GKRAddress → R)
    (baseLaw : ∀ address, Airbender.Compiler.FunctionalNative.MulDivCached.native.isBase address = true → values address = hom (physical address))
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank.address) = 0)
    (affine : ∀ definition ∈ Airbender.Compiler.FunctionalNative.MulDivCached.native.definitions, definition.Holds hom challenges values)
    (products : ∀ gate ∈ Airbender.Compiler.ProductNative.MulDivCached.native.gates, gate.Holds hom challenges values) :
    values Airbender.Compiler.MemoryNative.MulDivCached.native.memoryWriteOutput =
      maskProduct (hom ((Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data).get Airbender.MulDiv.importedConstraintsTraceColumns.execute))
      ((Airbender.MulDiv.importedConstraintsMemoryPorts.toList.map (Trace.writeToken Airbender.MulDiv.importedConstraintsTraceColumns (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data).get) ++
        [pcStateMemoryToken ⟨Trace.rawPair (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data).get Airbender.MulDiv.importedConstraintsTraceColumns.finalPC,
          Trace.rawPair (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data).get Airbender.MulDiv.importedConstraintsTraceColumns.finalTime⟩]).map
        (memoryTokenFingerprint hom challenges)).prod := by
  let assignment : TypedAssignment R := ⟨physical, values⟩
  have typedEq : assignment.value Airbender.Compiler.ConsumerNative.MulDivCached.native.typing hom = values := TypedAssignment.value_eq assignment Airbender.Compiler.ConsumerNative.MulDivCached.native.typing hom baseLaw
  have defined : ∀ definition ∈ Airbender.Compiler.MemoryNative.MulDivCached.native.definitions, definition.Holds hom challenges (assignment.value Airbender.Compiler.ConsumerNative.MulDivCached.native.typing hom) := by
    rw [typedEq, ← Airbender.Compiler.FunctionalLinksNative.MulDivCached.native.memoryDefinitionsAgree]
    exact affine
  have holds := products
  rw [← typedEq] at holds
  have reduced := Airbender.Compiler.MemoryNative.MulDivCached.native.memoryWriteSourceReduction hom challenges assignment defined (Airbender.Compiler.FunctionalLinksNative.MulDivCached.native.memoryCopies physical arithmetic) holds
  rw [typedEq] at reduced
  change values Airbender.Compiler.MemoryNative.MulDivCached.native.memoryWriteOutput = maskProduct (hom (Airbender.Compiler.MemoryNative.MulDivCached.native.sourceExecute.value (Airbender.Compiler.MemoryNative.MulDivCached.native.sourceValues physical)))
    (Airbender.Compiler.MemoryNative.MulDivCached.native.memoryWriteRows.map (fun row => row.fingerprint (Airbender.Compiler.MemoryNative.MulDivCached.native.sourceValues physical) hom challenges)).prod at reduced
  have executeSame : Airbender.Compiler.MemoryNative.MulDivCached.native.sourceExecute.value (Airbender.Compiler.MemoryNative.MulDivCached.native.sourceValues physical) =
      (Airbender.Compiler.CleanArithmeticNative.MulDivCached.native.environment physical data).get Airbender.MulDiv.importedConstraintsTraceColumns.execute :=
    (original_assignment physical data 4 (by decide +kernel)).symm
  rw [executeSame, write_products_from_base hom challenges physical data] at reduced
  exact reduced

end Airbender.Compiler.MemoryPortsNative.MulDivCached
