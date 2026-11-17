module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.MemoryTokens
public import Proven.GKRProtocol.FunctionalLinksNative.JumpBranchCached
public import Proven.Compiler.NativeBindings.JumpBranch
public import Proven.Compiler.NativeSatisfiable.JumpBranch
public import Proven.KernelRfl
public import Human.Compiler.MemoryPorts

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.MemoryPortsNative.JumpBranchCached
open Airbender Airbender.Compiler NativeMemoryBridge
set_option maxRecDepth 32768

/-- The imported affine definitions are the recipes of the imported capture. -/
theorem definitions_binding :
    MemoryNative.JumpBranchCached.native.definitions = definitionPrograms Captures.JumpBranch.imported.circuit := by
  kernel_rfl

/-- The imported product gates are the RAM-product recipes of the imported capture. -/
theorem gates_binding :
    ProductNative.JumpBranchCached.native.gates = productGates Captures.JumpBranch.imported.circuit := by
  kernel_rfl

/-- Every recipe reads its operands with the field role of the checked typing. -/
theorem typed : typingChecked ConsumerNative.JumpBranchCached.native.typing Captures.JumpBranch.imported.circuit = true := by
  decide +kernel

/-- The RAM output map names the reduced read and write outputs. Both are extension wires. -/
theorem outputs : NativeMemory.ramOutputs Captures.JumpBranch.imported.circuit =
    [MemoryNative.JumpBranchCached.native.memoryReadOutput, MemoryNative.JumpBranchCached.native.memoryWriteOutput] := by
  kernel_rfl

theorem outputs_extension :
    isBase ConsumerNative.JumpBranchCached.native.typing MemoryNative.JumpBranchCached.native.memoryReadOutput = false ∧
      isBase ConsumerNative.JumpBranchCached.native.typing MemoryNative.JumpBranchCached.native.memoryWriteOutput = false := by
  decide +kernel

/-- The source read rows are the port read tokens and the starting PC-state token of the model row. -/
theorem source_read_tokens (assignment : Nat → NativeArithmetic.F) (other : Source.MemoryValues) :
    MemoryNative.JumpBranchCached.native.memoryReadRows.map (fun row => row.token {other with original := assignment}) =
      NativeMemory.cpuReads (⟨.jumpBranchSlt, assignment⟩ : Trace.Row babyBearModulus Trace.PooledFamily) := by
  rfl

/-- The source write rows are the port write tokens and the final PC-state token of the model row. -/
theorem source_write_tokens (assignment : Nat → NativeArithmetic.F) (other : Source.MemoryValues) :
    MemoryNative.JumpBranchCached.native.memoryWriteRows.map (fun row => row.token {other with original := assignment}) =
      NativeMemory.cpuWrites (⟨.jumpBranchSlt, assignment⟩ : Trace.Row babyBearModulus Trace.PooledFamily) := by
  rfl

/-- The source execute field reads the model execute column. -/
theorem source_execute (assignment : Nat → NativeArithmetic.F) (other : Source.MemoryValues) :
    MemoryNative.JumpBranchCached.native.sourceExecute.value {other with original := assignment} =
      assignment Airbender.JumpBranchSlt.importedConstraintsTraceColumns.execute := by
  rfl

/-- The original indices of the memory rows and the execute field. -/
noncomputable def originalIndices : List Nat :=
  MemoryNative.JumpBranchCached.native.sourceExecute.originalIndices ++
    (MemoryNative.JumpBranchCached.native.memoryReadRows ++ MemoryNative.JumpBranchCached.native.memoryWriteRows).flatMap
      Source.MemoryRow.originalIndices

/-- Each original index of the memory rows has the placement of the imported capture. -/
theorem placement_checked : originalIndices.all (fun index =>
    Captures.JumpBranch.imported.circuit.placement_data.entries.toList.any fun entry =>
      decide (entry = (index, MemoryNative.JumpBranchCached.native.bank.address
        (MemoryNative.JumpBranchCached.native.sourcePlacement.original index)))) = true := by
  decide +kernel

theorem ram_products {R : Type} [CommRing R] (challenges : NativeMemory.Challenges R)
    (physical : GKRAddress → NativeArithmetic.F) (values : GKRAddress → R) (assignment : Nat → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Captures.JumpBranch.imported.circuit physical)
    (placement : NativeArithmetic.PlacementAgreement Captures.JumpBranch.imported.circuit physical assignment)
    (extension : NativeMemory.Holds Captures.JumpBranch.imported.circuit challenges physical values) :
    NativeMemory.RamProducts Captures.JumpBranch.imported.circuit challenges values
      (assignment Airbender.JumpBranchSlt.importedConstraintsTraceColumns.execute)
      (NativeMemory.cpuReads (⟨.jumpBranchSlt, assignment⟩ : Trace.Row babyBearModulus Trace.PooledFamily))
      (NativeMemory.cpuWrites (⟨.jumpBranchSlt, assignment⟩ : Trace.Row babyBearModulus Trace.PooledFamily)) := by
  let typed' : TypedAssignment R := ⟨physical, values⟩
  have defined : ∀ definition ∈ MemoryNative.JumpBranchCached.native.definitions,
      definition.Holds challenges.memory.embed (cacheChallenges challenges)
        (typed'.value ConsumerNative.JumpBranchCached.native.typing challenges.memory.embed) := by
    rw [definitions_binding]
    exact definitions_hold challenges _ physical values typed accepted extension
  have holds : ∀ gate ∈ ProductNative.JumpBranchCached.native.gates,
      gate.Holds challenges.memory.embed (cacheChallenges challenges)
        (typed'.value ConsumerNative.JumpBranchCached.native.typing challenges.memory.embed) := by
    rw [gates_binding]
    exact products_hold challenges _ physical values typed extension
  have copies := FunctionalLinksNative.JumpBranchCached.native.memoryCopies physical
    (NativeBindings.JumpBranch.scalar_gates physical accepted)
  have original := Source.MemoryPlacement.original_of_agreement
    MemoryNative.JumpBranchCached.native.sourcePlacement MemoryNative.JumpBranchCached.native.bank.address
    originalIndices placement_checked placement
  have rows : ∀ row ∈ MemoryNative.JumpBranchCached.native.memoryReadRows ++ MemoryNative.JumpBranchCached.native.memoryWriteRows,
      ∀ index ∈ row.originalIndices, assignment index =
        (MemoryNative.JumpBranchCached.native.sourceValues physical).original index := fun row member index used =>
    original index (List.mem_append_right _ (List.mem_flatMap.mpr ⟨row, member, used⟩))
  have execute : MemoryNative.JumpBranchCached.native.sourceExecute.value (MemoryNative.JumpBranchCached.native.sourceValues physical) =
      assignment Airbender.JumpBranchSlt.importedConstraintsTraceColumns.execute := by
    rw [← source_execute assignment (MemoryNative.JumpBranchCached.native.sourceValues physical)]
    exact (Source.MemoryField.withOriginal_value _ _ _ fun index used =>
      original index (List.mem_append_left _ used)).symm
  have readTokens : MemoryNative.JumpBranchCached.native.memoryReadRows.map
      (fun row => row.token (MemoryNative.JumpBranchCached.native.sourceValues physical)) =
      NativeMemory.cpuReads (⟨.jumpBranchSlt, assignment⟩ : Trace.Row babyBearModulus Trace.PooledFamily) := by
    rw [← source_read_tokens assignment (MemoryNative.JumpBranchCached.native.sourceValues physical)]
    exact (Source.MemoryRow.tokens_original _ _ _ fun row member => rows row (List.mem_append_left _ member)).symm
  have writeTokens : MemoryNative.JumpBranchCached.native.memoryWriteRows.map
      (fun row => row.token (MemoryNative.JumpBranchCached.native.sourceValues physical)) =
      NativeMemory.cpuWrites (⟨.jumpBranchSlt, assignment⟩ : Trace.Row babyBearModulus Trace.PooledFamily) := by
    rw [← source_write_tokens assignment (MemoryNative.JumpBranchCached.native.sourceValues physical)]
    exact (Source.MemoryRow.tokens_original _ _ _ fun row member => rows row (List.mem_append_right _ member)).symm
  have read := MemoryNative.JumpBranchCached.native.memoryReadSourceReduction challenges.memory.embed
    (cacheChallenges challenges) typed' defined copies holds
  have write := MemoryNative.JumpBranchCached.native.memoryWriteSourceReduction challenges.memory.embed
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
theorem satisfiable : JumpBranchCachedMemorySatisfiableClaim := by
  obtain ⟨physical, logical, accepted, placement⟩ := NativeSatisfiable.JumpBranch.witness
  let challenges : NativeMemory.Challenges NativeArithmetic.F := ⟨⟨RingHom.id _, 0, fun _ => 0, fun _ => 0⟩, 0⟩
  let values := FunctionalNative.JumpBranchCached.native.canonical challenges.memory.embed (cacheChallenges challenges) 0 physical
  have same : wires challenges ConsumerNative.JumpBranchCached.native.typing physical values = values :=
    FunctionalLinksNative.JumpBranchCached.native.assignment_value challenges.memory.embed (cacheChallenges challenges) 0 physical
  refine ⟨challenges, physical, values, ⟨.jumpBranchSlt, logical⟩, rfl, accepted, placement, ?_⟩
  rw [← same]
  apply holds_of_programs challenges _ physical values typed
  · rw [same, ← definitions_binding, ← FunctionalLinksNative.JumpBranchCached.native.memoryDefinitionsAgree]
    exact FunctionalNative.JumpBranchCached.native.canonical_affines _ _ 0 physical
      (NativeBindings.JumpBranch.scalar_gates physical accepted)
  · rw [same, ← gates_binding]
    exact FunctionalNative.JumpBranchCached.native.canonical_products _ _ 0 physical

end Airbender.Compiler.MemoryPortsNative.JumpBranchCached
