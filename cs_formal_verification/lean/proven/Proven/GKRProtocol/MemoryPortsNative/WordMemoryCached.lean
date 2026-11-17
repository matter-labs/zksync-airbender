module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.MemoryTokens
public import Proven.GKRProtocol.FunctionalLinksNative.WordMemoryCached
public import Proven.Compiler.NativeBindings.WordMemory
public import Proven.Compiler.NativeSatisfiable.WordMemory
public import Proven.KernelRfl
public import Human.Compiler.MemoryPorts

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.MemoryPortsNative.WordMemoryCached
open Airbender Airbender.Compiler NativeMemoryBridge
set_option maxRecDepth 32768

/-- The imported affine definitions are the recipes of the imported capture. -/
theorem definitions_binding :
    MemoryNative.WordMemoryCached.native.definitions = definitionPrograms Captures.WordMemory.imported.circuit := by
  kernel_rfl

/-- The imported product gates are the RAM-product recipes of the imported capture. -/
theorem gates_binding :
    ProductNative.WordMemoryCached.native.gates = productGates Captures.WordMemory.imported.circuit := by
  kernel_rfl

/-- Every recipe reads its operands with the field role of the checked typing. -/
theorem typed : typingChecked ConsumerNative.WordMemoryCached.native.typing Captures.WordMemory.imported.circuit = true := by
  decide +kernel

/-- The RAM output map names the reduced read and write outputs. Both are extension wires. -/
theorem outputs : NativeMemory.ramOutputs Captures.WordMemory.imported.circuit =
    [MemoryNative.WordMemoryCached.native.memoryReadOutput, MemoryNative.WordMemoryCached.native.memoryWriteOutput] := by
  kernel_rfl

theorem outputs_extension :
    isBase ConsumerNative.WordMemoryCached.native.typing MemoryNative.WordMemoryCached.native.memoryReadOutput = false ∧
      isBase ConsumerNative.WordMemoryCached.native.typing MemoryNative.WordMemoryCached.native.memoryWriteOutput = false := by
  decide +kernel

/-- The source read rows are the port read tokens and the starting PC-state token of the model row. -/
theorem source_read_tokens (assignment : Nat → NativeArithmetic.F) (other : Source.MemoryValues) :
    MemoryNative.WordMemoryCached.native.memoryReadRows.map (fun row => row.token {other with original := assignment}) =
      NativeMemory.cpuReads (⟨.wordMemory, assignment⟩ : Trace.Row babyBearModulus Trace.PooledFamily) := by
  simp [MemoryNative.WordMemoryCached.native.memoryReadRows, Airbender.WordMemory.importedConstraintsMemoryPorts,
    Airbender.WordMemory.importedConstraintsTraceColumns, Source.MemoryRow.token, Source.MemoryField.value,
    Source.LookupInput.value, NativeMemory.cpuReads, NativeMemory.stateToken, Trace.Row.reads,
    Trace.Row.ports, Trace.Row.columns, Trace.Row.start, Trace.CircuitLayout.ports,
    Trace.CircuitLayout.columns, Trace.readToken, Trace.rawPair, Trace.MemoryPort.readCode, Trace.WordColumns.code,
    Trace.WordColumns.evaluate, Trace.pairCode, Trace.MemoryAddress.code, sub_eq_add_neg,
    (by decide +kernel : (2 : NativeArithmetic.F).val = 2)]

/-- The source write rows are the port write tokens and the final PC-state token of the model row. -/
theorem source_write_tokens (assignment : Nat → NativeArithmetic.F) (other : Source.MemoryValues) :
    MemoryNative.WordMemoryCached.native.memoryWriteRows.map (fun row => row.token {other with original := assignment}) =
      NativeMemory.cpuWrites (⟨.wordMemory, assignment⟩ : Trace.Row babyBearModulus Trace.PooledFamily) := by
  simp [MemoryNative.WordMemoryCached.native.memoryWriteRows, Airbender.WordMemory.importedConstraintsMemoryPorts,
    Airbender.WordMemory.importedConstraintsTraceColumns, Source.MemoryRow.token, Source.MemoryField.value,
    Source.LookupInput.value, NativeMemory.cpuWrites, NativeMemory.stateToken, Trace.Row.writes,
    Trace.Row.ports, Trace.Row.columns, Trace.Row.finish, Trace.CircuitLayout.ports,
    Trace.CircuitLayout.columns, Trace.writeToken, Trace.rawPair, Trace.MemoryPort.writeCode, Trace.WordColumns.code,
    Trace.WordColumns.evaluate, Trace.pairCode, Trace.MemoryAddress.code, sub_eq_add_neg,
    (by decide +kernel : (2 : NativeArithmetic.F).val = 2)]

/-- The source execute field reads the model execute column. -/
theorem source_execute (assignment : Nat → NativeArithmetic.F) (other : Source.MemoryValues) :
    MemoryNative.WordMemoryCached.native.sourceExecute.value {other with original := assignment} =
      assignment Airbender.WordMemory.importedConstraintsTraceColumns.execute := by
  rfl

/-- The original indices of the memory rows and the execute field. -/
noncomputable def originalIndices : List Nat :=
  MemoryNative.WordMemoryCached.native.sourceExecute.originalIndices ++
    (MemoryNative.WordMemoryCached.native.memoryReadRows ++ MemoryNative.WordMemoryCached.native.memoryWriteRows).flatMap
      Source.MemoryRow.originalIndices

/-- Each original index of the memory rows has the placement of the imported capture. -/
theorem placement_checked : originalIndices.all (fun index =>
    Captures.WordMemory.imported.circuit.placement_data.entries.toList.any fun entry =>
      decide (entry = (index, MemoryNative.WordMemoryCached.native.bank.address
        (MemoryNative.WordMemoryCached.native.sourcePlacement.original index)))) = true := by
  decide +kernel

theorem ram_products {R : Type} [CommRing R] (challenges : NativeMemory.Challenges R)
    (physical : GKRAddress → NativeArithmetic.F) (values : GKRAddress → R) (assignment : Nat → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Captures.WordMemory.imported.circuit physical)
    (placement : NativeArithmetic.PlacementAgreement Captures.WordMemory.imported.circuit physical assignment)
    (extension : NativeMemory.Holds Captures.WordMemory.imported.circuit challenges physical values) :
    NativeMemory.RamProducts Captures.WordMemory.imported.circuit challenges values
      (assignment Airbender.WordMemory.importedConstraintsTraceColumns.execute)
      (NativeMemory.cpuReads (⟨.wordMemory, assignment⟩ : Trace.Row babyBearModulus Trace.PooledFamily))
      (NativeMemory.cpuWrites (⟨.wordMemory, assignment⟩ : Trace.Row babyBearModulus Trace.PooledFamily)) := by
  let typed' : TypedAssignment R := ⟨physical, values⟩
  have defined : ∀ definition ∈ MemoryNative.WordMemoryCached.native.definitions,
      definition.Holds challenges.memory.embed (cacheChallenges challenges)
        (typed'.value ConsumerNative.WordMemoryCached.native.typing challenges.memory.embed) := by
    rw [definitions_binding]
    exact definitions_hold challenges _ physical values typed accepted extension
  have holds : ∀ gate ∈ ProductNative.WordMemoryCached.native.gates,
      gate.Holds challenges.memory.embed (cacheChallenges challenges)
        (typed'.value ConsumerNative.WordMemoryCached.native.typing challenges.memory.embed) := by
    rw [gates_binding]
    exact products_hold challenges _ physical values typed extension
  have copies := FunctionalLinksNative.WordMemoryCached.native.memoryCopies physical
    (NativeBindings.WordMemory.scalar_gates physical accepted)
  have original := Source.MemoryPlacement.original_of_agreement
    MemoryNative.WordMemoryCached.native.sourcePlacement MemoryNative.WordMemoryCached.native.bank.address
    originalIndices placement_checked placement
  have rows : ∀ row ∈ MemoryNative.WordMemoryCached.native.memoryReadRows ++ MemoryNative.WordMemoryCached.native.memoryWriteRows,
      ∀ index ∈ row.originalIndices, assignment index =
        (MemoryNative.WordMemoryCached.native.sourceValues physical).original index := fun row member index used =>
    original index (List.mem_append_right _ (List.mem_flatMap.mpr ⟨row, member, used⟩))
  have execute : MemoryNative.WordMemoryCached.native.sourceExecute.value (MemoryNative.WordMemoryCached.native.sourceValues physical) =
      assignment Airbender.WordMemory.importedConstraintsTraceColumns.execute := by
    rw [← source_execute assignment (MemoryNative.WordMemoryCached.native.sourceValues physical)]
    exact (Source.MemoryField.withOriginal_value _ _ _ fun index used =>
      original index (List.mem_append_left _ used)).symm
  have readTokens : MemoryNative.WordMemoryCached.native.memoryReadRows.map
      (fun row => row.token (MemoryNative.WordMemoryCached.native.sourceValues physical)) =
      NativeMemory.cpuReads (⟨.wordMemory, assignment⟩ : Trace.Row babyBearModulus Trace.PooledFamily) := by
    rw [← source_read_tokens assignment (MemoryNative.WordMemoryCached.native.sourceValues physical)]
    exact (Source.MemoryRow.tokens_original _ _ _ fun row member => rows row (List.mem_append_left _ member)).symm
  have writeTokens : MemoryNative.WordMemoryCached.native.memoryWriteRows.map
      (fun row => row.token (MemoryNative.WordMemoryCached.native.sourceValues physical)) =
      NativeMemory.cpuWrites (⟨.wordMemory, assignment⟩ : Trace.Row babyBearModulus Trace.PooledFamily) := by
    rw [← source_write_tokens assignment (MemoryNative.WordMemoryCached.native.sourceValues physical)]
    exact (Source.MemoryRow.tokens_original _ _ _ fun row member => rows row (List.mem_append_right _ member)).symm
  have read := MemoryNative.WordMemoryCached.native.memoryReadSourceReduction challenges.memory.embed
    (cacheChallenges challenges) typed' defined copies holds
  have write := MemoryNative.WordMemoryCached.native.memoryWriteSourceReduction challenges.memory.embed
    (cacheChallenges challenges) typed' defined copies holds
  apply ram_products_of_outputs outputs
  · rw [← wires_extension challenges _ physical values outputs_extension.1]
    refine read.trans ?_
    rw [execute, ← readTokens, Source.MemoryRow.token_products]
    rfl
  · rw [← wires_extension challenges _ physical values outputs_extension.2]
    refine write.trans ?_
    rw [execute, ← writeTokens, Source.MemoryRow.token_products]
    rfl

/-- The canonical extension values of the arithmetic witness meet the memory premises. -/
theorem satisfiable : WordMemoryCachedMemorySatisfiableClaim := by
  obtain ⟨physical, logical, accepted, placement⟩ := NativeSatisfiable.WordMemory.witness
  let challenges : NativeMemory.Challenges NativeArithmetic.F := ⟨⟨RingHom.id _, 0, fun _ => 0, fun _ => 0⟩, 0⟩
  let values := FunctionalNative.WordMemoryCached.native.canonical challenges.memory.embed (cacheChallenges challenges) 0 physical
  have same : wires challenges ConsumerNative.WordMemoryCached.native.typing physical values = values :=
    FunctionalLinksNative.WordMemoryCached.native.assignment_value challenges.memory.embed (cacheChallenges challenges) 0 physical
  refine ⟨challenges, physical, values, ⟨.wordMemory, logical⟩, rfl, accepted, placement, ?_⟩
  rw [← same]
  apply holds_of_programs challenges _ physical values typed
  · rw [same, ← definitions_binding, ← FunctionalLinksNative.WordMemoryCached.native.memoryDefinitionsAgree]
    exact FunctionalNative.WordMemoryCached.native.canonical_affines _ _ 0 physical
      (NativeBindings.WordMemory.scalar_gates physical accepted)
  · rw [same, ← gates_binding]
    exact FunctionalNative.WordMemoryCached.native.canonical_products _ _ 0 physical

end Airbender.Compiler.MemoryPortsNative.WordMemoryCached
