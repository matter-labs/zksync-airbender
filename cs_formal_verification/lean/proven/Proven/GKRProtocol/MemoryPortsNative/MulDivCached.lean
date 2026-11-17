module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.MemoryTokens
public import Proven.GKRProtocol.FunctionalLinksNative.MulDivCached
public import Proven.Compiler.NativeBindings.MulDiv
public import Proven.Compiler.NativeSatisfiable.MulDiv
public import Proven.KernelRfl
public import Human.Compiler.MemoryPorts

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.MemoryPortsNative.MulDivCached
open Airbender Airbender.Compiler NativeMemoryBridge
set_option maxRecDepth 32768

/-- The imported affine definitions are the recipes of the imported capture. -/
theorem definitions_binding :
    MemoryNative.MulDivCached.native.definitions = definitionPrograms Captures.MulDiv.imported.circuit := by
  kernel_rfl

/-- The imported product gates are the RAM-product recipes of the imported capture. -/
theorem gates_binding :
    ProductNative.MulDivCached.native.gates = productGates Captures.MulDiv.imported.circuit := by
  kernel_rfl

/-- Every recipe reads its operands with the field role of the checked typing. -/
theorem typed : typingChecked (baseRoles ConsumerNative.MulDivCached.native.typing) Captures.MulDiv.imported.circuit = true := by
  decide +kernel

/-- The RAM output map names the reduced read and write outputs. Both are extension wires. -/
theorem outputs : NativeMemory.ramOutputs Captures.MulDiv.imported.circuit =
    [MemoryNative.MulDivCached.native.memoryReadOutput, MemoryNative.MulDivCached.native.memoryWriteOutput] := by
  kernel_rfl

theorem outputs_extension :
    isBase (baseRoles ConsumerNative.MulDivCached.native.typing) MemoryNative.MulDivCached.native.memoryReadOutput = false ∧
      isBase (baseRoles ConsumerNative.MulDivCached.native.typing) MemoryNative.MulDivCached.native.memoryWriteOutput = false := by
  decide +kernel

/-- The source read rows are the port read tokens and the starting PC-state token of the model row. -/
theorem source_read_tokens (assignment : Nat → NativeArithmetic.F) (other : Source.MemoryValues) :
    MemoryNative.MulDivCached.native.memoryReadRows.map (fun row => row.token {other with original := assignment}) =
      NativeMemory.cpuReads (⟨.mulDiv, assignment⟩ : Trace.Row babyBearModulus Trace.PooledFamily) := by
  rfl

/-- The source write rows are the port write tokens and the final PC-state token of the model row. -/
theorem source_write_tokens (assignment : Nat → NativeArithmetic.F) (other : Source.MemoryValues) :
    MemoryNative.MulDivCached.native.memoryWriteRows.map (fun row => row.token {other with original := assignment}) =
      NativeMemory.cpuWrites (⟨.mulDiv, assignment⟩ : Trace.Row babyBearModulus Trace.PooledFamily) := by
  rfl

/-- The source execute field reads the model execute column. -/
theorem source_execute (assignment : Nat → NativeArithmetic.F) (other : Source.MemoryValues) :
    MemoryNative.MulDivCached.native.sourceExecute.value {other with original := assignment} =
      assignment Airbender.MulDiv.importedConstraintsTraceColumns.execute := by
  rfl

/-- The original indices of the memory rows and the execute field. -/
noncomputable def originalIndices : List Nat :=
  MemoryNative.MulDivCached.native.sourceExecute.originalIndices ++
    (MemoryNative.MulDivCached.native.memoryReadRows ++ MemoryNative.MulDivCached.native.memoryWriteRows).flatMap
      Source.MemoryRow.originalIndices

/-- Each original index of the memory rows has the placement of the imported capture. -/
theorem placement_checked : originalIndices.all (fun index =>
    Captures.MulDiv.imported.circuit.placement_data.entries.toList.any fun entry =>
      decide (entry = (index, MemoryNative.MulDivCached.native.bank.address
        (MemoryNative.MulDivCached.native.sourcePlacement.original index)))) = true := by
  decide +kernel

theorem ram_products {R : Type} [CommRing R] (challenges : NativeMemory.Challenges R)
    (physical : GKRAddress → NativeArithmetic.F) (values : GKRAddress → R) (assignment : Nat → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Captures.MulDiv.imported.circuit physical)
    (placement : NativeArithmetic.PlacementAgreement Captures.MulDiv.imported.circuit physical assignment)
    (extension : NativeMemory.Holds Captures.MulDiv.imported.circuit challenges physical values) :
    NativeMemory.RamProducts Captures.MulDiv.imported.circuit challenges values
      (assignment Airbender.MulDiv.importedConstraintsTraceColumns.execute)
      (NativeMemory.cpuReads (⟨.mulDiv, assignment⟩ : Trace.Row babyBearModulus Trace.PooledFamily))
      (NativeMemory.cpuWrites (⟨.mulDiv, assignment⟩ : Trace.Row babyBearModulus Trace.PooledFamily)) := by
  let typed' : TypedAssignment R := ⟨physical, values⟩
  have defined : ∀ definition ∈ MemoryNative.MulDivCached.native.definitions,
      definition.Holds challenges.memory.embed (cacheChallenges challenges)
        (wires challenges (baseRoles ConsumerNative.MulDivCached.native.typing) physical values) := by
    rw [definitions_binding]
    exact definitions_hold challenges _ physical values typed accepted extension
  have holds : ∀ gate ∈ ProductNative.MulDivCached.native.gates,
      gate.Holds challenges.memory.embed (cacheChallenges challenges)
        (wires challenges (baseRoles ConsumerNative.MulDivCached.native.typing) physical values) := by
    rw [gates_binding]
    exact products_hold challenges _ physical values typed extension
  rw [wires_typed] at defined holds
  have copies := FunctionalLinksNative.MulDivCached.native.memoryCopies physical
    (NativeBindings.MulDiv.scalar_gates physical accepted)
  have original := Source.MemoryPlacement.original_of_agreement
    MemoryNative.MulDivCached.native.sourcePlacement MemoryNative.MulDivCached.native.bank.address
    originalIndices placement_checked placement
  have rows : ∀ row ∈ MemoryNative.MulDivCached.native.memoryReadRows ++ MemoryNative.MulDivCached.native.memoryWriteRows,
      ∀ index ∈ row.originalIndices, assignment index =
        (MemoryNative.MulDivCached.native.sourceValues physical).original index := fun row member index used =>
    original index (List.mem_append_right _ (List.mem_flatMap.mpr ⟨row, member, used⟩))
  have execute : MemoryNative.MulDivCached.native.sourceExecute.value (MemoryNative.MulDivCached.native.sourceValues physical) =
      assignment Airbender.MulDiv.importedConstraintsTraceColumns.execute := by
    rw [← source_execute assignment (MemoryNative.MulDivCached.native.sourceValues physical)]
    exact (Source.MemoryField.withOriginal_value _ _ _ fun index used =>
      original index (List.mem_append_left _ used)).symm
  have readTokens : MemoryNative.MulDivCached.native.memoryReadRows.map
      (fun row => row.token (MemoryNative.MulDivCached.native.sourceValues physical)) =
      NativeMemory.cpuReads (⟨.mulDiv, assignment⟩ : Trace.Row babyBearModulus Trace.PooledFamily) := by
    rw [← source_read_tokens assignment (MemoryNative.MulDivCached.native.sourceValues physical)]
    exact (Source.MemoryRow.tokens_original _ _ _ fun row member => rows row (List.mem_append_left _ member)).symm
  have writeTokens : MemoryNative.MulDivCached.native.memoryWriteRows.map
      (fun row => row.token (MemoryNative.MulDivCached.native.sourceValues physical)) =
      NativeMemory.cpuWrites (⟨.mulDiv, assignment⟩ : Trace.Row babyBearModulus Trace.PooledFamily) := by
    rw [← source_write_tokens assignment (MemoryNative.MulDivCached.native.sourceValues physical)]
    exact (Source.MemoryRow.tokens_original _ _ _ fun row member => rows row (List.mem_append_right _ member)).symm
  have read := MemoryNative.MulDivCached.native.memoryReadSourceReduction challenges.memory.embed
    (cacheChallenges challenges) typed' defined copies holds
  have write := MemoryNative.MulDivCached.native.memoryWriteSourceReduction challenges.memory.embed
    (cacheChallenges challenges) typed' defined copies holds
  apply ram_products_of_outputs outputs
  · rw [← wires_extension challenges _ physical values outputs_extension.1, wires_typed]
    refine read.trans ?_
    rw [execute, ← readTokens, Source.MemoryRow.token_products]
    rfl
  · rw [← wires_extension challenges _ physical values outputs_extension.2, wires_typed]
    refine write.trans ?_
    rw [execute, ← writeTokens, Source.MemoryRow.token_products]
    rfl

/-- The canonical extension values of the arithmetic witness meet the memory premises. -/
theorem satisfiable : MulDivCachedMemorySatisfiableClaim := by
  obtain ⟨physical, logical, accepted, placement⟩ := NativeSatisfiable.MulDiv.witness
  let challenges : NativeMemory.Challenges NativeArithmetic.F := ⟨⟨RingHom.id _, 0, fun _ => 0, fun _ => 0⟩, 0⟩
  let values := FunctionalNative.MulDivCached.native.canonical challenges.memory.embed (cacheChallenges challenges) 0 physical
  have same : wires challenges (baseRoles ConsumerNative.MulDivCached.native.typing) physical values = values :=
    (wires_typed _ _ _ _).trans
      (FunctionalLinksNative.MulDivCached.native.assignment_value challenges.memory.embed (cacheChallenges challenges) 0 physical)
  refine ⟨challenges, physical, values, ⟨.mulDiv, logical⟩, rfl, accepted, placement, ?_⟩
  rw [← same]
  apply holds_of_programs challenges _ physical values typed
  · rw [same, ← definitions_binding, ← FunctionalLinksNative.MulDivCached.native.memoryDefinitionsAgree]
    exact FunctionalNative.MulDivCached.native.canonical_affines _ _ 0 physical
      (NativeBindings.MulDiv.scalar_gates physical accepted)
  · rw [same, ← gates_binding]
    exact FunctionalNative.MulDivCached.native.canonical_products _ _ 0 physical

end Airbender.Compiler.MemoryPortsNative.MulDivCached
