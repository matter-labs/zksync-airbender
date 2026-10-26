import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.SubwordMemoryUncached
import Airbender.Proofs.GKRProtocol.MemoryTokens
import Airbender.Proofs.GKRProtocol.MemoryNative.SubwordMemoryUncached
import Airbender.Proofs.GKRProtocol.FunctionalLinksNative.SubwordMemoryUncached
import Airbender.Proofs.GKRProtocol.NativeWitness
import Airbender.Review.Circuits.SubwordMemory.Artifact

namespace Airbender.Compiler.MemoryPortsNative.SubwordMemoryUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem source_read_tokens (assignment : Nat → Source.BaseField) (other : Source.MemoryValues) :
    (Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.memoryReadRows.map (fun row => row.token {other with original := assignment})) =
      Airbender.SubwordMemory.importedConstraintsMemoryPorts.toList.map (Trace.readToken assignment) ++
        [pcStateMemoryToken ⟨Trace.rawPair assignment Airbender.SubwordMemory.importedConstraintsTraceColumns.initialPC,
          Trace.rawPair assignment Airbender.SubwordMemory.importedConstraintsTraceColumns.initialTime⟩] := by
  simp [Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.memoryReadRows, Airbender.SubwordMemory.importedConstraintsMemoryPorts, Airbender.SubwordMemory.importedConstraintsTraceColumns, Source.MemoryRow.token, Source.MemoryField.value, Source.LookupInput.value, Trace.readToken, Trace.rawPair, Trace.MemoryPort.readCode, Trace.WordColumns.code, Trace.WordColumns.evaluate, Trace.pairCode, Trace.MemoryAddress.code, pcStateMemoryToken, sub_eq_add_neg]

theorem source_write_tokens (assignment : Nat → Source.BaseField) (other : Source.MemoryValues) :
    (Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.memoryWriteRows.map (fun row => row.token {other with original := assignment})) =
      Airbender.SubwordMemory.importedConstraintsMemoryPorts.toList.map (Trace.writeToken Airbender.SubwordMemory.importedConstraintsTraceColumns assignment) ++
        [pcStateMemoryToken ⟨Trace.rawPair assignment Airbender.SubwordMemory.importedConstraintsTraceColumns.finalPC,
          Trace.rawPair assignment Airbender.SubwordMemory.importedConstraintsTraceColumns.finalTime⟩] := by
  simp [Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.memoryWriteRows, Airbender.SubwordMemory.importedConstraintsMemoryPorts, Airbender.SubwordMemory.importedConstraintsTraceColumns, Source.MemoryRow.token, Source.MemoryField.value, Source.LookupInput.value, Trace.writeToken, Trace.rawPair, Trace.MemoryPort.writeCode, Trace.WordColumns.code, Trace.WordColumns.evaluate, Trace.pairCode, Trace.MemoryAddress.code, pcStateMemoryToken, sub_eq_add_neg]

theorem original_columns : (List.range 62).all (fun index =>
    decide (Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.placement index) =
      Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.bank.address (Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.sourcePlacement.original index))) = true := by decide +kernel

theorem original_assignment (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (index : Nat) (bounded : index < 62) :
    (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data).get index = (Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.sourceValues physical).original index := by
  exact congrArg physical (of_decide_eq_true (List.all_eq_true.mp original_columns index (List.mem_range.mpr bounded)))

theorem read_original_indices : Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.memoryReadRows.all
    (fun row => row.originalIndices.all (fun index => decide (index < 62))) = true := by decide +kernel

theorem read_tokens_from_base (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField) :
    Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.memoryReadRows.map (fun row => row.token (Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.sourceValues physical)) =
      Airbender.SubwordMemory.importedConstraintsMemoryPorts.toList.map (Trace.readToken (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data).get) ++
        [pcStateMemoryToken ⟨Trace.rawPair (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data).get Airbender.SubwordMemory.importedConstraintsTraceColumns.initialPC,
          Trace.rawPair (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data).get Airbender.SubwordMemory.importedConstraintsTraceColumns.initialTime⟩] := by
  rw [← source_read_tokens (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data).get (Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.sourceValues physical)]
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

theorem write_original_indices : Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.memoryWriteRows.all
    (fun row => row.originalIndices.all (fun index => decide (index < 62))) = true := by decide +kernel

theorem write_tokens_from_base (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField) :
    Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.memoryWriteRows.map (fun row => row.token (Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.sourceValues physical)) =
      Airbender.SubwordMemory.importedConstraintsMemoryPorts.toList.map (Trace.writeToken Airbender.SubwordMemory.importedConstraintsTraceColumns (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data).get) ++
        [pcStateMemoryToken ⟨Trace.rawPair (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data).get Airbender.SubwordMemory.importedConstraintsTraceColumns.finalPC,
          Trace.rawPair (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data).get Airbender.SubwordMemory.importedConstraintsTraceColumns.finalTime⟩] := by
  rw [← source_write_tokens (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data).get (Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.sourceValues physical)]
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
    (Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.memoryReadRows.map (fun row => row.fingerprint (Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.sourceValues physical) hom challenges)).prod =
      ((Airbender.SubwordMemory.importedConstraintsMemoryPorts.toList.map (Trace.readToken (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data).get) ++
        [pcStateMemoryToken ⟨Trace.rawPair (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data).get Airbender.SubwordMemory.importedConstraintsTraceColumns.initialPC,
          Trace.rawPair (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data).get Airbender.SubwordMemory.importedConstraintsTraceColumns.initialTime⟩]).map
        (memoryTokenFingerprint hom challenges)).prod := by
  rw [← Source.MemoryRow.token_products Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.memoryReadRows (Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.sourceValues physical) hom challenges,
    read_tokens_from_base physical data]

theorem write_products_from_base {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField) :
    (Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.memoryWriteRows.map (fun row => row.fingerprint (Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.sourceValues physical) hom challenges)).prod =
      ((Airbender.SubwordMemory.importedConstraintsMemoryPorts.toList.map (Trace.writeToken Airbender.SubwordMemory.importedConstraintsTraceColumns (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data).get) ++
        [pcStateMemoryToken ⟨Trace.rawPair (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data).get Airbender.SubwordMemory.importedConstraintsTraceColumns.finalPC,
          Trace.rawPair (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data).get Airbender.SubwordMemory.importedConstraintsTraceColumns.finalTime⟩]).map
        (memoryTokenFingerprint hom challenges)).prod := by
  rw [← Source.MemoryRow.token_products Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.memoryWriteRows (Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.sourceValues physical) hom challenges,
    write_tokens_from_base physical data]

theorem read_output_logical {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (values : GKRAddress → R)
    (baseLaw : ∀ address, Airbender.Compiler.FunctionalNative.SubwordMemoryUncached.native.isBase address = true → values address = hom (physical address))
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.bank.address) = 0)
    (affine : ∀ definition ∈ Airbender.Compiler.FunctionalNative.SubwordMemoryUncached.native.definitions, definition.Holds hom challenges values)
    (products : ∀ gate ∈ Airbender.Compiler.ProductNative.SubwordMemoryUncached.native.gates, gate.Holds hom challenges values) :
    values Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.memoryReadOutput =
      maskProduct (hom ((Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data).get Airbender.SubwordMemory.importedConstraintsTraceColumns.execute))
      ((Airbender.SubwordMemory.importedConstraintsMemoryPorts.toList.map (Trace.readToken (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data).get) ++
        [pcStateMemoryToken ⟨Trace.rawPair (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data).get Airbender.SubwordMemory.importedConstraintsTraceColumns.initialPC,
          Trace.rawPair (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data).get Airbender.SubwordMemory.importedConstraintsTraceColumns.initialTime⟩]).map
        (memoryTokenFingerprint hom challenges)).prod := by
  let assignment : TypedAssignment R := ⟨physical, values⟩
  have typedEq : assignment.value Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing hom = values := TypedAssignment.value_eq assignment Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing hom baseLaw
  have defined : ∀ definition ∈ Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.definitions, definition.Holds hom challenges (assignment.value Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing hom) := by
    rw [typedEq, ← Airbender.Compiler.FunctionalLinksNative.SubwordMemoryUncached.native.memoryDefinitionsAgree]
    exact affine
  have holds := products
  rw [← typedEq] at holds
  have reduced := Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.memoryReadSourceReduction hom challenges assignment defined (Airbender.Compiler.FunctionalLinksNative.SubwordMemoryUncached.native.memoryCopies physical arithmetic) holds
  rw [typedEq] at reduced
  change values Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.memoryReadOutput = maskProduct (hom (Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.sourceExecute.value (Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.sourceValues physical)))
    (Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.memoryReadRows.map (fun row => row.fingerprint (Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.sourceValues physical) hom challenges)).prod at reduced
  have executeSame : Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.sourceExecute.value (Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.sourceValues physical) =
      (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data).get Airbender.SubwordMemory.importedConstraintsTraceColumns.execute :=
    (original_assignment physical data 4 (by decide +kernel)).symm
  rw [executeSame, read_products_from_base hom challenges physical data] at reduced
  exact reduced

theorem write_output_logical {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (values : GKRAddress → R)
    (baseLaw : ∀ address, Airbender.Compiler.FunctionalNative.SubwordMemoryUncached.native.isBase address = true → values address = hom (physical address))
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.SubwordMemoryUncached.native.bank.address) = 0)
    (affine : ∀ definition ∈ Airbender.Compiler.FunctionalNative.SubwordMemoryUncached.native.definitions, definition.Holds hom challenges values)
    (products : ∀ gate ∈ Airbender.Compiler.ProductNative.SubwordMemoryUncached.native.gates, gate.Holds hom challenges values) :
    values Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.memoryWriteOutput =
      maskProduct (hom ((Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data).get Airbender.SubwordMemory.importedConstraintsTraceColumns.execute))
      ((Airbender.SubwordMemory.importedConstraintsMemoryPorts.toList.map (Trace.writeToken Airbender.SubwordMemory.importedConstraintsTraceColumns (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data).get) ++
        [pcStateMemoryToken ⟨Trace.rawPair (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data).get Airbender.SubwordMemory.importedConstraintsTraceColumns.finalPC,
          Trace.rawPair (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data).get Airbender.SubwordMemory.importedConstraintsTraceColumns.finalTime⟩]).map
        (memoryTokenFingerprint hom challenges)).prod := by
  let assignment : TypedAssignment R := ⟨physical, values⟩
  have typedEq : assignment.value Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing hom = values := TypedAssignment.value_eq assignment Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing hom baseLaw
  have defined : ∀ definition ∈ Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.definitions, definition.Holds hom challenges (assignment.value Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing hom) := by
    rw [typedEq, ← Airbender.Compiler.FunctionalLinksNative.SubwordMemoryUncached.native.memoryDefinitionsAgree]
    exact affine
  have holds := products
  rw [← typedEq] at holds
  have reduced := Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.memoryWriteSourceReduction hom challenges assignment defined (Airbender.Compiler.FunctionalLinksNative.SubwordMemoryUncached.native.memoryCopies physical arithmetic) holds
  rw [typedEq] at reduced
  change values Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.memoryWriteOutput = maskProduct (hom (Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.sourceExecute.value (Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.sourceValues physical)))
    (Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.memoryWriteRows.map (fun row => row.fingerprint (Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.sourceValues physical) hom challenges)).prod at reduced
  have executeSame : Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.sourceExecute.value (Airbender.Compiler.MemoryNative.SubwordMemoryUncached.native.sourceValues physical) =
      (Airbender.Compiler.CleanArithmeticNative.SubwordMemoryUncached.native.environment physical data).get Airbender.SubwordMemory.importedConstraintsTraceColumns.execute :=
    (original_assignment physical data 4 (by decide +kernel)).symm
  rw [executeSame, write_products_from_base hom challenges physical data] at reduced
  exact reduced

end Airbender.Compiler.MemoryPortsNative.SubwordMemoryUncached
