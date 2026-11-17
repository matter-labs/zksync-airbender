module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.MemoryTokens
public import Proven.GKRProtocol.NativeMemoryExcluded
public import Proven.GKRProtocol.FunctionalLinksNative.UnifiedCached
public import Proven.Compiler.NativeBindings.Unified
public import Proven.Compiler.NativeSatisfiable.Unified
public import Proven.KernelRfl
public import Human.Compiler.MemoryPorts

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.MemoryPortsNative.UnifiedCached
open Airbender Airbender.Compiler NativeMemoryBridge
set_option maxRecDepth 32768

/-- The imported affine definitions are the recipes of the imported capture. -/
theorem definitions_binding :
    MemoryNative.UnifiedCached.native.definitions = definitionPrograms Captures.Unified.imported.circuit := by
  kernel_rfl

/-- The imported product gates are the RAM-product recipes of the imported capture. -/
theorem gates_binding :
    ProductNative.UnifiedCached.native.gates = productGates Captures.Unified.imported.circuit := by
  kernel_rfl

/-- The initialization subgraph has its own interface. -/
noncomputable abbrev initialization : List GKRAddress := initializationWires Captures.Unified.imported.circuit

/-- Every recipe outside the initialization subgraph reads its operands with the field role of the checked typing. -/
theorem typed : typingCheckedExcept (baseRoles ConsumerNative.UnifiedCached.native.typing) Captures.Unified.imported.circuit
    initialization = true := by
  decide +kernel

/-- The initialization subgraph reads only its own and base wires. No other recipe reads it. -/
theorem definitions_separated : (definitionPrograms Captures.Unified.imported.circuit).all (fun definition =>
    separated (baseRoles ConsumerNative.UnifiedCached.native.typing) initialization definition.output
      (definitionAddresses definition)) = true := by
  decide +kernel

theorem products_separated : (productGates Captures.Unified.imported.circuit).all (fun gate =>
    separated (baseRoles ConsumerNative.UnifiedCached.native.typing) initialization (productOutput gate)
      (productAddresses gate)) = true := by
  decide +kernel

/-- The RAM output map names the reduced read and write outputs. Both are extension wires. -/
theorem outputs : NativeMemory.ramOutputs Captures.Unified.imported.circuit =
    [MemoryNative.UnifiedCached.native.memoryReadOutput, MemoryNative.UnifiedCached.native.memoryWriteOutput] := by
  kernel_rfl

theorem outputs_extension :
    isBase (baseRoles ConsumerNative.UnifiedCached.native.typing) MemoryNative.UnifiedCached.native.memoryReadOutput = false ∧
      isBase (baseRoles ConsumerNative.UnifiedCached.native.typing) MemoryNative.UnifiedCached.native.memoryWriteOutput = false := by
  decide +kernel

theorem outputs_outside :
    initialization.contains MemoryNative.UnifiedCached.native.memoryReadOutput = false ∧
      initialization.contains MemoryNative.UnifiedCached.native.memoryWriteOutput = false := by
  decide +kernel

/-- The source read rows are the port read tokens and the starting PC-state token of the model row. -/
theorem source_read_tokens (assignment : Nat → NativeArithmetic.F) (other : Source.MemoryValues) :
    MemoryNative.UnifiedCached.native.memoryReadRows.map (fun row => row.token {other with original := assignment}) =
      NativeMemory.cpuReads (⟨.machine, assignment⟩ : Trace.Row babyBearModulus Trace.UnifiedFamily) := by
  rfl

/-- The source write rows are the port write tokens and the final PC-state token of the model row. -/
theorem source_write_tokens (assignment : Nat → NativeArithmetic.F) (other : Source.MemoryValues) :
    MemoryNative.UnifiedCached.native.memoryWriteRows.map (fun row => row.token {other with original := assignment}) =
      NativeMemory.cpuWrites (⟨.machine, assignment⟩ : Trace.Row babyBearModulus Trace.UnifiedFamily) := by
  rfl

/-- The source execute field reads the model execute column. -/
theorem source_execute (assignment : Nat → NativeArithmetic.F) (other : Source.MemoryValues) :
    MemoryNative.UnifiedCached.native.sourceExecute.value {other with original := assignment} =
      assignment Airbender.UnifiedReduced.importedConstraintsTraceColumns.execute := by
  rfl

/-- The original indices of the memory rows and the execute field. -/
noncomputable def originalIndices : List Nat :=
  MemoryNative.UnifiedCached.native.sourceExecute.originalIndices ++
    (MemoryNative.UnifiedCached.native.memoryReadRows ++ MemoryNative.UnifiedCached.native.memoryWriteRows).flatMap
      Source.MemoryRow.originalIndices

/-- Each original index of the memory rows has the placement of the imported capture. -/
theorem placement_checked : originalIndices.all (fun index =>
    Captures.Unified.imported.circuit.placement_data.entries.toList.any fun entry =>
      decide (entry = (index, MemoryNative.UnifiedCached.native.bank.address
        (MemoryNative.UnifiedCached.native.sourcePlacement.original index)))) = true := by
  decide +kernel

theorem ram_products {R : Type} [CommRing R] (challenges : NativeMemory.Challenges R)
    (physical : GKRAddress → NativeArithmetic.F) (values : GKRAddress → R) (assignment : Nat → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Captures.Unified.imported.circuit physical)
    (placement : NativeArithmetic.PlacementAgreement Captures.Unified.imported.circuit physical assignment)
    (extension : NativeMemory.Holds Captures.Unified.imported.circuit challenges physical values) :
    NativeMemory.RamProducts Captures.Unified.imported.circuit challenges values
      (assignment Airbender.UnifiedReduced.importedConstraintsTraceColumns.execute)
      (NativeMemory.cpuReads (⟨.machine, assignment⟩ : Trace.Row babyBearModulus Trace.UnifiedFamily))
      (NativeMemory.cpuWrites (⟨.machine, assignment⟩ : Trace.Row babyBearModulus Trace.UnifiedFamily)) := by
  let canonical := FunctionalNative.UnifiedCached.native.canonical challenges.memory.embed (cacheChallenges challenges)
    0 physical
  have canonicalBase : ∀ address, isBase (baseRoles ConsumerNative.UnifiedCached.native.typing) address = true →
      canonical address = challenges.embed (physical address) := fun address role =>
    FunctionalNative.UnifiedCached.native.canonical_base _ _ 0 physical address
      ((isBase_baseRoles _ address).symm.trans role)
  let typed' : TypedAssignment R := ⟨physical, spliced initialization canonical values⟩
  have defined : ∀ definition ∈ MemoryNative.UnifiedCached.native.definitions,
      definition.Holds challenges.memory.embed (cacheChallenges challenges)
        (wires challenges (baseRoles ConsumerNative.UnifiedCached.native.typing) physical (spliced initialization canonical values)) := by
    rw [definitions_binding]
    refine definitions_hold_spliced challenges _ physical values canonical initialization typed definitions_separated
      accepted extension canonicalBase ?_
    rw [← definitions_binding, ← FunctionalLinksNative.UnifiedCached.native.memoryDefinitionsAgree]
    exact FunctionalNative.UnifiedCached.native.canonical_affines _ _ 0 physical
      (NativeBindings.Unified.scalar_gates physical accepted)
  have holds : ∀ gate ∈ ProductNative.UnifiedCached.native.gates,
      gate.Holds challenges.memory.embed (cacheChallenges challenges)
        (wires challenges (baseRoles ConsumerNative.UnifiedCached.native.typing) physical (spliced initialization canonical values)) := by
    rw [gates_binding]
    refine products_hold_spliced challenges _ physical values canonical initialization typed products_separated
      extension canonicalBase ?_
    rw [← gates_binding]
    exact FunctionalNative.UnifiedCached.native.canonical_products _ _ 0 physical
  rw [wires_typed] at defined holds
  have copies := FunctionalLinksNative.UnifiedCached.native.memoryCopies physical
    (NativeBindings.Unified.scalar_gates physical accepted)
  have original := Source.MemoryPlacement.original_of_agreement
    MemoryNative.UnifiedCached.native.sourcePlacement MemoryNative.UnifiedCached.native.bank.address
    originalIndices placement_checked placement
  have rows : ∀ row ∈ MemoryNative.UnifiedCached.native.memoryReadRows ++ MemoryNative.UnifiedCached.native.memoryWriteRows,
      ∀ index ∈ row.originalIndices, assignment index =
        (MemoryNative.UnifiedCached.native.sourceValues physical).original index := fun row member index used =>
    original index (List.mem_append_right _ (List.mem_flatMap.mpr ⟨row, member, used⟩))
  have execute : MemoryNative.UnifiedCached.native.sourceExecute.value (MemoryNative.UnifiedCached.native.sourceValues physical) =
      assignment Airbender.UnifiedReduced.importedConstraintsTraceColumns.execute := by
    rw [← source_execute assignment (MemoryNative.UnifiedCached.native.sourceValues physical)]
    exact (Source.MemoryField.withOriginal_value _ _ _ fun index used =>
      original index (List.mem_append_left _ used)).symm
  have readTokens : MemoryNative.UnifiedCached.native.memoryReadRows.map
      (fun row => row.token (MemoryNative.UnifiedCached.native.sourceValues physical)) =
      NativeMemory.cpuReads (⟨.machine, assignment⟩ : Trace.Row babyBearModulus Trace.UnifiedFamily) := by
    rw [← source_read_tokens assignment (MemoryNative.UnifiedCached.native.sourceValues physical)]
    exact (Source.MemoryRow.tokens_original _ _ _ fun row member => rows row (List.mem_append_left _ member)).symm
  have writeTokens : MemoryNative.UnifiedCached.native.memoryWriteRows.map
      (fun row => row.token (MemoryNative.UnifiedCached.native.sourceValues physical)) =
      NativeMemory.cpuWrites (⟨.machine, assignment⟩ : Trace.Row babyBearModulus Trace.UnifiedFamily) := by
    rw [← source_write_tokens assignment (MemoryNative.UnifiedCached.native.sourceValues physical)]
    exact (Source.MemoryRow.tokens_original _ _ _ fun row member => rows row (List.mem_append_right _ member)).symm
  have read := MemoryNative.UnifiedCached.native.memoryReadSourceReduction challenges.memory.embed
    (cacheChallenges challenges) typed' defined copies holds
  have write := MemoryNative.UnifiedCached.native.memoryWriteSourceReduction challenges.memory.embed
    (cacheChallenges challenges) typed' defined copies holds
  apply ram_products_of_outputs outputs
  · rw [← wires_extension challenges _ physical values outputs_extension.1,
      ← spliced_values challenges _ physical values canonical initialization _ outputs_outside.1, wires_typed]
    refine read.trans ?_
    rw [execute, ← readTokens, Source.MemoryRow.token_products]
    rfl
  · rw [← wires_extension challenges _ physical values outputs_extension.2,
      ← spliced_values challenges _ physical values canonical initialization _ outputs_outside.2, wires_typed]
    refine write.trans ?_
    rw [execute, ← writeTokens, Source.MemoryRow.token_products]
    rfl

/-- The canonical extension values of the arithmetic witness meet the memory premises. -/
theorem satisfiable : UnifiedCachedMemorySatisfiableClaim := by
  obtain ⟨physical, logical, accepted, placement⟩ := NativeSatisfiable.Unified.witness
  let challenges : NativeMemory.Challenges NativeArithmetic.F := ⟨⟨RingHom.id _, 0, fun _ => 0, fun _ => 0⟩, 0⟩
  let values := FunctionalNative.UnifiedCached.native.canonical challenges.memory.embed (cacheChallenges challenges) 0 physical
  have same : wires challenges (baseRoles ConsumerNative.UnifiedCached.native.typing) physical values = values :=
    (wires_typed _ _ _ _).trans
      (FunctionalLinksNative.UnifiedCached.native.assignment_value challenges.memory.embed (cacheChallenges challenges) 0 physical)
  refine ⟨challenges, physical, values, ⟨.machine, logical⟩, accepted, placement, ?_⟩
  rw [← same]
  apply holds_of_programs challenges _ physical values typed
  · rw [same, ← definitions_binding, ← FunctionalLinksNative.UnifiedCached.native.memoryDefinitionsAgree]
    exact FunctionalNative.UnifiedCached.native.canonical_affines _ _ 0 physical
      (NativeBindings.Unified.scalar_gates physical accepted)
  · rw [same, ← gates_binding]
    exact FunctionalNative.UnifiedCached.native.canonical_products _ _ 0 physical

end Airbender.Compiler.MemoryPortsNative.UnifiedCached
