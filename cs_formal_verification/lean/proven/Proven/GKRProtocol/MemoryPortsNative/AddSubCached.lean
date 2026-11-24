module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.MemoryTokens
public import Proven.GKRProtocol.FunctionalLinksNative.AddSubCached
public import Proven.Compiler.NativeBindings.AddSub
public import Proven.Compiler.NativeSatisfiable.AddSub
public import Proven.KernelRfl
public import Human.Compiler.MemoryPorts

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.MemoryPortsNative.AddSubCached
open Airbender Airbender.Compiler NativeMemoryBridge
set_option maxRecDepth 32768

/-- The imported affine definitions are the recipes of the imported capture. -/
theorem definitions_binding :
    MemoryNative.AddSubCached.native.definitions = definitionPrograms Captures.AddSub.imported.circuit := by
  kernel_rfl

/-- The imported product gates are the RAM-product recipes of the imported capture. -/
theorem gates_binding :
    ProductNative.AddSubCached.native.gates = productGates Captures.AddSub.imported.circuit := by
  kernel_rfl

/-- Every recipe reads its operands with the field role of the checked typing. -/
theorem typed : typingChecked (baseRoles ConsumerNative.AddSubCached.native.typing) Captures.AddSub.imported.circuit = true := by
  decide +kernel

/-- The RAM output map names the reduced read and write outputs. Both are extension wires. -/
theorem outputs : NativeMemory.ramOutputs Captures.AddSub.imported.circuit =
    [MemoryNative.AddSubCached.native.memoryReadOutput, MemoryNative.AddSubCached.native.memoryWriteOutput] := by
  kernel_rfl

theorem outputs_extension :
    isBase (baseRoles ConsumerNative.AddSubCached.native.typing) MemoryNative.AddSubCached.native.memoryReadOutput = false ∧
      isBase (baseRoles ConsumerNative.AddSubCached.native.typing) MemoryNative.AddSubCached.native.memoryWriteOutput = false := by
  decide +kernel

/-- The source read rows are the port read tokens and the starting PC-state token of the model row. -/
theorem source_read_tokens (assignment : Nat → NativeArithmetic.F) (other : Source.MemoryValues) :
    MemoryNative.AddSubCached.native.memoryReadRows.map (fun row => row.token {other with original := assignment}) =
      NativeMemory.cpuReads (⟨.addSub, assignment⟩ : Trace.Row babyBearModulus Trace.PooledFamily) := by
  rfl

/-- The source write rows are the port write tokens and the final PC-state token of the model row. -/
theorem source_write_tokens (assignment : Nat → NativeArithmetic.F) (other : Source.MemoryValues) :
    MemoryNative.AddSubCached.native.memoryWriteRows.map (fun row => row.token {other with original := assignment}) =
      NativeMemory.cpuWrites (⟨.addSub, assignment⟩ : Trace.Row babyBearModulus Trace.PooledFamily) := by
  rfl

/-- The source execute field reads the model execute column. -/
theorem source_execute (assignment : Nat → NativeArithmetic.F) (other : Source.MemoryValues) :
    MemoryNative.AddSubCached.native.sourceExecute.value {other with original := assignment} =
      assignment Airbender.AddSub.importedConstraintsTraceColumns.execute := by
  rfl

/-- The original indices of the memory rows and the execute field. -/
noncomputable def originalIndices : List Nat :=
  MemoryNative.AddSubCached.native.sourceExecute.originalIndices ++
    (MemoryNative.AddSubCached.native.memoryReadRows ++ MemoryNative.AddSubCached.native.memoryWriteRows).flatMap
      Source.MemoryRow.originalIndices

/-- Each original index of the memory rows has the placement of the imported capture. -/
theorem placement_checked : originalIndices.all (fun index =>
    Captures.AddSub.imported.circuit.placement_data.entries.toList.any fun entry =>
      decide (entry = (index, MemoryNative.AddSubCached.native.bank.address
        (MemoryNative.AddSubCached.native.sourcePlacement.original index)))) = true := by
  decide +kernel

theorem ram_products {R : Type} [CommRing R] (challenges : NativeMemory.Challenges R)
    (physical : GKRAddress → NativeArithmetic.F) (values : GKRAddress → R) (assignment : Nat → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Captures.AddSub.imported.circuit physical)
    (placement : NativeArithmetic.PlacementAgreement Captures.AddSub.imported.circuit physical assignment)
    (extension : NativeMemory.Holds Captures.AddSub.imported.circuit challenges physical values) :
    NativeMemory.RamProducts Captures.AddSub.imported.circuit challenges values
      (assignment Airbender.AddSub.importedConstraintsTraceColumns.execute)
      (NativeMemory.cpuReads (⟨.addSub, assignment⟩ : Trace.Row babyBearModulus Trace.PooledFamily))
      (NativeMemory.cpuWrites (⟨.addSub, assignment⟩ : Trace.Row babyBearModulus Trace.PooledFamily)) := by
  let typed' : TypedAssignment R := ⟨physical, values⟩
  have defined : ∀ definition ∈ MemoryNative.AddSubCached.native.definitions,
      definition.Holds challenges.memory.embed (cacheChallenges challenges)
        (wires challenges (baseRoles ConsumerNative.AddSubCached.native.typing) physical values) := by
    rw [definitions_binding]
    exact definitions_hold challenges _ physical values typed accepted extension
  have holds : ∀ gate ∈ ProductNative.AddSubCached.native.gates,
      gate.Holds challenges.memory.embed (cacheChallenges challenges)
        (wires challenges (baseRoles ConsumerNative.AddSubCached.native.typing) physical values) := by
    rw [gates_binding]
    exact products_hold challenges _ physical values typed extension
  rw [wires_typed] at defined holds
  have copies := FunctionalLinksNative.AddSubCached.native.memoryCopies physical
    (NativeBindings.AddSub.scalar_gates physical accepted)
  have original := Source.MemoryPlacement.original_of_agreement
    MemoryNative.AddSubCached.native.sourcePlacement MemoryNative.AddSubCached.native.bank.address
    originalIndices placement_checked placement
  have rows : ∀ row ∈ MemoryNative.AddSubCached.native.memoryReadRows ++ MemoryNative.AddSubCached.native.memoryWriteRows,
      ∀ index ∈ row.originalIndices, assignment index =
        (MemoryNative.AddSubCached.native.sourceValues physical).original index := fun row member index used =>
    original index (List.mem_append_right _ (List.mem_flatMap.mpr ⟨row, member, used⟩))
  have execute : MemoryNative.AddSubCached.native.sourceExecute.value (MemoryNative.AddSubCached.native.sourceValues physical) =
      assignment Airbender.AddSub.importedConstraintsTraceColumns.execute := by
    rw [← source_execute assignment (MemoryNative.AddSubCached.native.sourceValues physical)]
    exact (Source.MemoryField.withOriginal_value _ _ _ fun index used =>
      original index (List.mem_append_left _ used)).symm
  have readTokens : MemoryNative.AddSubCached.native.memoryReadRows.map
      (fun row => row.token (MemoryNative.AddSubCached.native.sourceValues physical)) =
      NativeMemory.cpuReads (⟨.addSub, assignment⟩ : Trace.Row babyBearModulus Trace.PooledFamily) := by
    rw [← source_read_tokens assignment (MemoryNative.AddSubCached.native.sourceValues physical)]
    exact (Source.MemoryRow.tokens_original _ _ _ fun row member => rows row (List.mem_append_left _ member)).symm
  have writeTokens : MemoryNative.AddSubCached.native.memoryWriteRows.map
      (fun row => row.token (MemoryNative.AddSubCached.native.sourceValues physical)) =
      NativeMemory.cpuWrites (⟨.addSub, assignment⟩ : Trace.Row babyBearModulus Trace.PooledFamily) := by
    rw [← source_write_tokens assignment (MemoryNative.AddSubCached.native.sourceValues physical)]
    exact (Source.MemoryRow.tokens_original _ _ _ fun row member => rows row (List.mem_append_right _ member)).symm
  have read := MemoryNative.AddSubCached.native.memoryReadSourceReduction challenges.memory.embed
    (cacheChallenges challenges) typed' defined copies holds
  have write := MemoryNative.AddSubCached.native.memoryWriteSourceReduction challenges.memory.embed
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
theorem satisfiable : AddSubCachedMemorySatisfiableClaim := by
  obtain ⟨physical, logical, accepted, placement⟩ := NativeSatisfiable.AddSub.witness
  let challenges : NativeMemory.Challenges NativeArithmetic.F := ⟨⟨RingHom.id _, 0, fun _ => 0, fun _ => 0⟩, 0⟩
  let values := FunctionalNative.AddSubCached.native.canonical challenges.memory.embed (cacheChallenges challenges) 0 physical
  have same : wires challenges (baseRoles ConsumerNative.AddSubCached.native.typing) physical values = values :=
    (wires_typed _ _ _ _).trans
      (FunctionalLinksNative.AddSubCached.native.assignment_value challenges.memory.embed (cacheChallenges challenges) 0 physical)
  refine ⟨challenges, physical, values, ⟨.addSub, logical⟩, rfl, accepted, placement, ?_⟩
  rw [← same]
  apply holds_of_programs challenges _ physical values typed
  · rw [same, ← definitions_binding, ← FunctionalLinksNative.AddSubCached.native.memoryDefinitionsAgree]
    exact FunctionalNative.AddSubCached.native.canonical_affines _ _ 0 physical
      (NativeBindings.AddSub.scalar_gates physical accepted)
  · rw [same, ← gates_binding]
    exact FunctionalNative.AddSubCached.native.canonical_products _ _ 0 physical

end Airbender.Compiler.MemoryPortsNative.AddSubCached
