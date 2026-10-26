import Airbender.Proofs.GKRProtocol.MemoryValueCongruence
import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.BlakeGUncached
import Airbender.Proofs.GKRProtocol.MemoryNative.BlakeGUncached
import Airbender.Proofs.GKRProtocol.MemoryTokens
import Airbender.Proofs.GKRProtocol.FunctionalLinksNative.BlakeGUncached
import Airbender.Proofs.GKRProtocol.NativeWitness
import Airbender.Review.Helpers.Delegation.Requests

namespace Airbender.Compiler.WorkerPortsNative.BlakeGUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def originalIndices : List Nat := [0] ++
  (Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadRows ++ Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteRows).flatMap Source.MemoryRow.originalIndices

theorem original_columns : originalIndices.all (fun index =>
    decide (Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.placement index) =
      Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank.address (Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement.original index))) = true := by decide +kernel

theorem history_columns : ((List.finRange Airbender.Blake2G.importedConstraintsMemoryPorts.size).all (fun index =>
    (List.finRange 2).all (fun limb => decide
      (Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.placement
        ((Airbender.Blake2G.importedConstraintsMemoryPorts[index.val]).clock.previous[limb.val])) =
       Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank.address (Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement.readTimestamp index.val limb))))) = true := by decide +kernel

noncomputable def logicalValues (assignment : Nat → Source.BaseField) (other : Source.MemoryValues) : Source.MemoryValues :=
  { other with
    original := assignment
    readTimestamp := fun query limb =>
      if bounded : query < Airbender.Blake2G.importedConstraintsMemoryPorts.size then
        assignment ((Airbender.Blake2G.importedConstraintsMemoryPorts[query]).clock.previous[limb.val])
      else 0 }

theorem source_read_tokens (assignment : Nat → Source.BaseField) (other : Source.MemoryValues) :
    (Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadRows.map (fun row => row.token (logicalValues assignment other))) =
      Airbender.Blake2G.importedConstraintsMemoryPorts.toList.map (Trace.readToken assignment) ++
        [(Delegation.Requests.fulfillment (⟨.blakeG, assignment⟩ : Delegation.Row babyBearModulus)).issued] := by
  simp [Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadRows, Source.MemoryRow.token,
    Source.MemoryField.value, Source.LookupInput.value, logicalValues, Trace.readToken, Trace.rawPair,
    Trace.MemoryPort.readCode, Trace.WordColumns.code, Trace.WordColumns.evaluate, Trace.MemoryAddress.code,
    Verification.IndirectPort.rawAddress, Delegation.Requests.fulfillment,
    Delegation.Requests.csr, Delegation.Row.columns, Delegation.Requests.Request.issued,
    Delegation.Requests.Request.token, Airbender.Blake2G.importedConstraintsMemoryPorts,
    Airbender.Blake2G.importedConstraintsDelegationColumns]
  all_goals decide +kernel

theorem source_write_tokens (assignment : Nat → Source.BaseField) (other : Source.MemoryValues) :
    (Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteRows.map (fun row => row.token (logicalValues assignment other))) =
      Airbender.Blake2G.importedConstraintsMemoryPorts.toList.map ((⟨.blakeG, assignment⟩ : Delegation.Row babyBearModulus).writeToken) ++
        [(Delegation.Requests.fulfillment (⟨.blakeG, assignment⟩ : Delegation.Row babyBearModulus)).empty] := by
  simp [Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteRows, Source.MemoryRow.token,
    Source.MemoryField.value, Source.LookupInput.value, logicalValues, Delegation.Row.writeToken, Trace.rawPair,
    Trace.MemoryPort.writeCode, Trace.WordColumns.code, Trace.WordColumns.evaluate, Trace.MemoryAddress.code,
    Verification.IndirectPort.rawAddress, Delegation.Requests.fulfillment,
    Delegation.Requests.csr, Delegation.Row.columns, Delegation.Requests.Request.empty,
    Delegation.Requests.Request.token, Airbender.Blake2G.importedConstraintsMemoryPorts,
    Airbender.Blake2G.importedConstraintsDelegationColumns]
  all_goals decide +kernel

theorem original_assignment (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (index : Nat) (used : index ∈ originalIndices) :
    (Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourceValues physical).original index =
      (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data).get index := by
  exact (congrArg physical (of_decide_eq_true (List.all_eq_true.mp original_columns index used))).symm

theorem history_assignment (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (index : Fin Airbender.Blake2G.importedConstraintsMemoryPorts.size) (limb : Fin 2) :
    (Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourceValues physical).readTimestamp index.val limb =
      (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data).get
        ((Airbender.Blake2G.importedConstraintsMemoryPorts[index.val]).clock.previous[limb.val]) := by
  exact (congrArg physical (of_decide_eq_true (List.all_eq_true.mp
    (List.all_eq_true.mp history_columns index (List.mem_finRange index)) limb (List.mem_finRange limb)))).symm

theorem history_indices :
    (Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadRows ++ Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteRows).all
      (fun row => row.fields.all (fun field => field.historyIndices.all
        (fun index => decide (index.1 < Airbender.Blake2G.importedConstraintsMemoryPorts.size)))) = true := by decide +kernel

theorem row_token_from_base (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (row : Source.MemoryRow)
    (included : row ∈ Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadRows ++ Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteRows) :
    row.token (Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourceValues physical) =
      row.token (logicalValues (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data).get
        (Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourceValues physical)) := by
  apply Source.MemoryRow.token_congr
  intro field member
  apply Source.MemoryField.value_congr_scoped
  · intro index used
    apply original_assignment physical data index
    change index ∈ [0] ++ (Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadRows ++ Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteRows).flatMap Source.MemoryRow.originalIndices
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨row, included, ?_⟩
    exact List.mem_flatMap.mpr ⟨field, member, used⟩
  · intro index used
    have bounded := of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp
      (List.all_eq_true.mp history_indices row included) field member) index used)
    change _ = if guard : index.1 < Airbender.Blake2G.importedConstraintsMemoryPorts.size then _ else 0
    rw [dif_pos bounded]
    exact history_assignment physical data ⟨index.1, bounded⟩ index.2
  · rfl
  · rfl
  · rfl

theorem read_tokens_from_base (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField) :
    Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadRows.map (fun row => row.token (Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourceValues physical)) =
      Airbender.Blake2G.importedConstraintsMemoryPorts.toList.map (Trace.readToken (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data).get) ++ [(Delegation.Requests.fulfillment (⟨.blakeG, (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data).get⟩ : Delegation.Row babyBearModulus)).issued] := by
  rw [← source_read_tokens (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data).get (Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourceValues physical)]
  apply List.map_congr_left
  intro row member
  apply row_token_from_base
  exact List.mem_append_left _ member

theorem read_products_from_base {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField) :
    (Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadRows.map (fun row => row.fingerprint (Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourceValues physical) hom challenges)).prod =
      ((Airbender.Blake2G.importedConstraintsMemoryPorts.toList.map (Trace.readToken (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data).get) ++ [(Delegation.Requests.fulfillment (⟨.blakeG, (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data).get⟩ : Delegation.Row babyBearModulus)).issued]).map (memoryTokenFingerprint hom challenges)).prod := by
  rw [← Source.MemoryRow.token_products Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadRows (Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourceValues physical) hom challenges,
    read_tokens_from_base physical data]

theorem write_tokens_from_base (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField) :
    Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteRows.map (fun row => row.token (Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourceValues physical)) =
      Airbender.Blake2G.importedConstraintsMemoryPorts.toList.map ((⟨.blakeG, (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data).get⟩ : Delegation.Row babyBearModulus).writeToken) ++ [(Delegation.Requests.fulfillment (⟨.blakeG, (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data).get⟩ : Delegation.Row babyBearModulus)).empty] := by
  rw [← source_write_tokens (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data).get (Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourceValues physical)]
  apply List.map_congr_left
  intro row member
  apply row_token_from_base
  exact List.mem_append_right _ member

theorem write_products_from_base {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField) :
    (Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteRows.map (fun row => row.fingerprint (Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourceValues physical) hom challenges)).prod =
      ((Airbender.Blake2G.importedConstraintsMemoryPorts.toList.map ((⟨.blakeG, (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data).get⟩ : Delegation.Row babyBearModulus).writeToken) ++ [(Delegation.Requests.fulfillment (⟨.blakeG, (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data).get⟩ : Delegation.Row babyBearModulus)).empty]).map (memoryTokenFingerprint hom challenges)).prod := by
  rw [← Source.MemoryRow.token_products Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteRows (Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourceValues physical) hom challenges,
    write_tokens_from_base physical data]

theorem read_output_logical {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (values : GKRAddress → R)
    (baseLaw : ∀ address, Airbender.Compiler.FunctionalNative.BlakeGUncached.native.isBase address = true → values address = hom (physical address))
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.bank.address) = 0)
    (affine : ∀ definition ∈ Airbender.Compiler.FunctionalNative.BlakeGUncached.native.definitions, definition.Holds hom challenges values)
    (products : ∀ gate ∈ Airbender.Compiler.ProductNative.BlakeGUncached.native.gates, gate.Holds hom challenges values) :
    values Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadOutput =
      maskProduct (hom ((Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data).get Airbender.Blake2G.importedConstraintsDelegationColumns.execute))
      ((Airbender.Blake2G.importedConstraintsMemoryPorts.toList.map (Trace.readToken (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data).get) ++ [(Delegation.Requests.fulfillment (⟨.blakeG, (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data).get⟩ : Delegation.Row babyBearModulus)).issued]).map
        (memoryTokenFingerprint hom challenges)).prod := by
  let assignment : TypedAssignment R := ⟨physical, values⟩
  have typedEq : assignment.value Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing hom = values := TypedAssignment.value_eq assignment Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing hom baseLaw
  have defined : ∀ definition ∈ Airbender.Compiler.MemoryNative.BlakeGUncached.native.definitions, definition.Holds hom challenges (assignment.value Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing hom) := by
    rw [typedEq, ← Airbender.Compiler.FunctionalLinksNative.BlakeGUncached.native.memoryDefinitionsAgree]
    exact affine
  have holds := products
  rw [← typedEq] at holds
  have reduced := Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadSourceReduction hom challenges assignment defined (Airbender.Compiler.FunctionalLinksNative.BlakeGUncached.native.memoryCopies physical arithmetic) holds
  rw [typedEq] at reduced
  change values Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadOutput = maskProduct (hom (Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourceExecute.value (Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourceValues physical)))
    (Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryReadRows.map (fun row => row.fingerprint (Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourceValues physical) hom challenges)).prod at reduced
  have executeSame : Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourceExecute.value (Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourceValues physical) =
      (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data).get Airbender.Blake2G.importedConstraintsDelegationColumns.execute :=
    original_assignment physical data 0 (List.mem_append_left _ (List.mem_cons_self))
  rw [executeSame, read_products_from_base hom challenges physical data] at reduced
  exact reduced

theorem write_output_logical {R : Type} [CommRing R]
    (hom : Source.BaseField →+* R) (challenges : CacheChallenges R)
    (physical : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (values : GKRAddress → R)
    (baseLaw : ∀ address, Airbender.Compiler.FunctionalNative.BlakeGUncached.native.isBase address = true → values address = hom (physical address))
    (arithmetic : ∀ gate ∈ Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.artifact.gates, gate.expressionResidual (physical ∘ Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.bank.address) = 0)
    (affine : ∀ definition ∈ Airbender.Compiler.FunctionalNative.BlakeGUncached.native.definitions, definition.Holds hom challenges values)
    (products : ∀ gate ∈ Airbender.Compiler.ProductNative.BlakeGUncached.native.gates, gate.Holds hom challenges values) :
    values Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteOutput =
      maskProduct (hom ((Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data).get Airbender.Blake2G.importedConstraintsDelegationColumns.execute))
      ((Airbender.Blake2G.importedConstraintsMemoryPorts.toList.map ((⟨.blakeG, (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data).get⟩ : Delegation.Row babyBearModulus).writeToken) ++ [(Delegation.Requests.fulfillment (⟨.blakeG, (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data).get⟩ : Delegation.Row babyBearModulus)).empty]).map
        (memoryTokenFingerprint hom challenges)).prod := by
  let assignment : TypedAssignment R := ⟨physical, values⟩
  have typedEq : assignment.value Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing hom = values := TypedAssignment.value_eq assignment Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing hom baseLaw
  have defined : ∀ definition ∈ Airbender.Compiler.MemoryNative.BlakeGUncached.native.definitions, definition.Holds hom challenges (assignment.value Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing hom) := by
    rw [typedEq, ← Airbender.Compiler.FunctionalLinksNative.BlakeGUncached.native.memoryDefinitionsAgree]
    exact affine
  have holds := products
  rw [← typedEq] at holds
  have reduced := Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteSourceReduction hom challenges assignment defined (Airbender.Compiler.FunctionalLinksNative.BlakeGUncached.native.memoryCopies physical arithmetic) holds
  rw [typedEq] at reduced
  change values Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteOutput = maskProduct (hom (Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourceExecute.value (Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourceValues physical)))
    (Airbender.Compiler.MemoryNative.BlakeGUncached.native.memoryWriteRows.map (fun row => row.fingerprint (Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourceValues physical) hom challenges)).prod at reduced
  have executeSame : Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourceExecute.value (Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourceValues physical) =
      (Airbender.Compiler.CleanArithmeticNative.BlakeGUncached.native.environment physical data).get Airbender.Blake2G.importedConstraintsDelegationColumns.execute :=
    original_assignment physical data 0 (List.mem_append_left _ (List.mem_cons_self))
  rw [executeSame, write_products_from_base hom challenges physical data] at reduced
  exact reduced

end Airbender.Compiler.WorkerPortsNative.BlakeGUncached
