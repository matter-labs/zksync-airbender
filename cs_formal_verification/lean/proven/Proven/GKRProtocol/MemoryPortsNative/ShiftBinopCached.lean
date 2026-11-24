module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.MemoryTokens
public import Proven.GKRProtocol.FunctionalLinksNative.ShiftBinopCached
public import Proven.Compiler.NativeBindings.ShiftBinop
public import Proven.Compiler.NativeSatisfiable.ShiftBinop
public import Proven.KernelRfl
public import Human.Compiler.MemoryPorts

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.MemoryPortsNative.ShiftBinopCached
open Airbender Airbender.Compiler NativeMemoryBridge
set_option maxRecDepth 32768

/-- The imported affine definitions are the recipes of the imported capture. -/
theorem definitions_binding :
    MemoryNative.ShiftBinopCached.native.definitions = definitionPrograms Captures.ShiftBinop.imported.circuit := by
  kernel_rfl

/-- The imported product gates are the RAM-product recipes of the imported capture. -/
theorem gates_binding :
    ProductNative.ShiftBinopCached.native.gates = productGates Captures.ShiftBinop.imported.circuit := by
  kernel_rfl

/-- Every recipe reads its operands with the field role of the checked typing. -/
theorem typed : typingChecked (baseRoles ConsumerNative.ShiftBinopCached.native.typing) Captures.ShiftBinop.imported.circuit = true := by
  decide +kernel

/-- The RAM output map names the reduced read and write outputs. Both are extension wires. -/
theorem outputs : NativeMemory.ramOutputs Captures.ShiftBinop.imported.circuit =
    [MemoryNative.ShiftBinopCached.native.memoryReadOutput, MemoryNative.ShiftBinopCached.native.memoryWriteOutput] := by
  kernel_rfl

theorem outputs_extension :
    isBase (baseRoles ConsumerNative.ShiftBinopCached.native.typing) MemoryNative.ShiftBinopCached.native.memoryReadOutput = false ∧
      isBase (baseRoles ConsumerNative.ShiftBinopCached.native.typing) MemoryNative.ShiftBinopCached.native.memoryWriteOutput = false := by
  decide +kernel

/-- The source read rows are the port read tokens and the starting PC-state token of the model row. -/
theorem source_read_tokens (assignment : Nat → NativeArithmetic.F) (other : Source.MemoryValues) :
    MemoryNative.ShiftBinopCached.native.memoryReadRows.map (fun row => row.token {other with original := assignment}) =
      NativeMemory.cpuReads (⟨.shiftBinop, assignment⟩ : Trace.Row babyBearModulus Trace.PooledFamily) := by
  rfl

/-- The source write rows are the port write tokens and the final PC-state token of the model row. -/
theorem source_write_tokens (assignment : Nat → NativeArithmetic.F) (other : Source.MemoryValues) :
    MemoryNative.ShiftBinopCached.native.memoryWriteRows.map (fun row => row.token {other with original := assignment}) =
      NativeMemory.cpuWrites (⟨.shiftBinop, assignment⟩ : Trace.Row babyBearModulus Trace.PooledFamily) := by
  rfl

/-- The source execute field reads the model execute column. -/
theorem source_execute (assignment : Nat → NativeArithmetic.F) (other : Source.MemoryValues) :
    MemoryNative.ShiftBinopCached.native.sourceExecute.value {other with original := assignment} =
      assignment Airbender.ShiftBinop.importedConstraintsTraceColumns.execute := by
  rfl

/-- The original indices of the memory rows and the execute field. -/
noncomputable def originalIndices : List Nat :=
  MemoryNative.ShiftBinopCached.native.sourceExecute.originalIndices ++
    (MemoryNative.ShiftBinopCached.native.memoryReadRows ++ MemoryNative.ShiftBinopCached.native.memoryWriteRows).flatMap
      Source.MemoryRow.originalIndices

/-- Each original index of the memory rows has the placement of the imported capture. -/
theorem placement_checked : originalIndices.all (fun index =>
    Captures.ShiftBinop.imported.circuit.placement_data.entries.toList.any fun entry =>
      decide (entry = (index, MemoryNative.ShiftBinopCached.native.bank.address
        (MemoryNative.ShiftBinopCached.native.sourcePlacement.original index)))) = true := by
  decide +kernel

theorem ram_products {R : Type} [CommRing R] (challenges : NativeMemory.Challenges R)
    (physical : GKRAddress → NativeArithmetic.F) (values : GKRAddress → R) (assignment : Nat → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds Captures.ShiftBinop.imported.circuit physical)
    (placement : NativeArithmetic.PlacementAgreement Captures.ShiftBinop.imported.circuit physical assignment)
    (extension : NativeMemory.Holds Captures.ShiftBinop.imported.circuit challenges physical values) :
    NativeMemory.RamProducts Captures.ShiftBinop.imported.circuit challenges values
      (assignment Airbender.ShiftBinop.importedConstraintsTraceColumns.execute)
      (NativeMemory.cpuReads (⟨.shiftBinop, assignment⟩ : Trace.Row babyBearModulus Trace.PooledFamily))
      (NativeMemory.cpuWrites (⟨.shiftBinop, assignment⟩ : Trace.Row babyBearModulus Trace.PooledFamily)) := by
  let typed' : TypedAssignment R := ⟨physical, values⟩
  have defined : ∀ definition ∈ MemoryNative.ShiftBinopCached.native.definitions,
      definition.Holds challenges.memory.embed (cacheChallenges challenges)
        (wires challenges (baseRoles ConsumerNative.ShiftBinopCached.native.typing) physical values) := by
    rw [definitions_binding]
    exact definitions_hold challenges _ physical values typed accepted extension
  have holds : ∀ gate ∈ ProductNative.ShiftBinopCached.native.gates,
      gate.Holds challenges.memory.embed (cacheChallenges challenges)
        (wires challenges (baseRoles ConsumerNative.ShiftBinopCached.native.typing) physical values) := by
    rw [gates_binding]
    exact products_hold challenges _ physical values typed extension
  rw [wires_typed] at defined holds
  have copies := FunctionalLinksNative.ShiftBinopCached.native.memoryCopies physical
    (NativeBindings.ShiftBinop.scalar_gates physical accepted)
  have original := Source.MemoryPlacement.original_of_agreement
    MemoryNative.ShiftBinopCached.native.sourcePlacement MemoryNative.ShiftBinopCached.native.bank.address
    originalIndices placement_checked placement
  have rows : ∀ row ∈ MemoryNative.ShiftBinopCached.native.memoryReadRows ++ MemoryNative.ShiftBinopCached.native.memoryWriteRows,
      ∀ index ∈ row.originalIndices, assignment index =
        (MemoryNative.ShiftBinopCached.native.sourceValues physical).original index := fun row member index used =>
    original index (List.mem_append_right _ (List.mem_flatMap.mpr ⟨row, member, used⟩))
  have execute : MemoryNative.ShiftBinopCached.native.sourceExecute.value (MemoryNative.ShiftBinopCached.native.sourceValues physical) =
      assignment Airbender.ShiftBinop.importedConstraintsTraceColumns.execute := by
    rw [← source_execute assignment (MemoryNative.ShiftBinopCached.native.sourceValues physical)]
    exact (Source.MemoryField.withOriginal_value _ _ _ fun index used =>
      original index (List.mem_append_left _ used)).symm
  have readTokens : MemoryNative.ShiftBinopCached.native.memoryReadRows.map
      (fun row => row.token (MemoryNative.ShiftBinopCached.native.sourceValues physical)) =
      NativeMemory.cpuReads (⟨.shiftBinop, assignment⟩ : Trace.Row babyBearModulus Trace.PooledFamily) := by
    rw [← source_read_tokens assignment (MemoryNative.ShiftBinopCached.native.sourceValues physical)]
    exact (Source.MemoryRow.tokens_original _ _ _ fun row member => rows row (List.mem_append_left _ member)).symm
  have writeTokens : MemoryNative.ShiftBinopCached.native.memoryWriteRows.map
      (fun row => row.token (MemoryNative.ShiftBinopCached.native.sourceValues physical)) =
      NativeMemory.cpuWrites (⟨.shiftBinop, assignment⟩ : Trace.Row babyBearModulus Trace.PooledFamily) := by
    rw [← source_write_tokens assignment (MemoryNative.ShiftBinopCached.native.sourceValues physical)]
    exact (Source.MemoryRow.tokens_original _ _ _ fun row member => rows row (List.mem_append_right _ member)).symm
  have read := MemoryNative.ShiftBinopCached.native.memoryReadSourceReduction challenges.memory.embed
    (cacheChallenges challenges) typed' defined copies holds
  have write := MemoryNative.ShiftBinopCached.native.memoryWriteSourceReduction challenges.memory.embed
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
theorem satisfiable : ShiftBinopCachedMemorySatisfiableClaim := by
  obtain ⟨physical, logical, accepted, placement⟩ := NativeSatisfiable.ShiftBinop.witness
  let challenges : NativeMemory.Challenges NativeArithmetic.F := ⟨⟨RingHom.id _, 0, fun _ => 0, fun _ => 0⟩, 0⟩
  let values := FunctionalNative.ShiftBinopCached.native.canonical challenges.memory.embed (cacheChallenges challenges) 0 physical
  have same : wires challenges (baseRoles ConsumerNative.ShiftBinopCached.native.typing) physical values = values :=
    (wires_typed _ _ _ _).trans
      (FunctionalLinksNative.ShiftBinopCached.native.assignment_value challenges.memory.embed (cacheChallenges challenges) 0 physical)
  refine ⟨challenges, physical, values, ⟨.shiftBinop, logical⟩, rfl, accepted, placement, ?_⟩
  rw [← same]
  apply holds_of_programs challenges _ physical values typed
  · rw [same, ← definitions_binding, ← FunctionalLinksNative.ShiftBinopCached.native.memoryDefinitionsAgree]
    exact FunctionalNative.ShiftBinopCached.native.canonical_affines _ _ 0 physical
      (NativeBindings.ShiftBinop.scalar_gates physical accepted)
  · rw [same, ← gates_binding]
    exact FunctionalNative.ShiftBinopCached.native.canonical_products _ _ 0 physical

end Airbender.Compiler.MemoryPortsNative.ShiftBinopCached
