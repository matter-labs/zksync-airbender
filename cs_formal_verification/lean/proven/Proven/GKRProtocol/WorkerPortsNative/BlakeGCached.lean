module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.NativeMemoryWorkers
public import Proven.GKRProtocol.ProductNative.BlakeGCached
public import Proven.KernelRfl
public import Human.Compiler.WorkerMemoryPorts

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.WorkerPortsNative.BlakeGCached
open Airbender Airbender.Compiler NativeMemoryBridge
set_option maxRecDepth 32768

/-- The cached capture. -/
noncomputable abbrev circuit : Circuit := Captures.BlakeG.imported.circuit

/-- Base-field caches and gates of the capture write its base-field wires. -/
noncomputable abbrev roles : GKRAddress → Bool := structuralRoles circuit

/-- The imported product gates are the RAM-product recipes of the imported capture. -/
theorem gates_binding : ProductNative.BlakeGCached.native.gates = productGates circuit := by
  kernel_rfl

/-- Every recipe reads its operands with the structural field roles. -/
theorem typed : typingChecked roles circuit = true := by
  decide +kernel

/-- The RAM output map of the capture. -/
theorem outputs : NativeMemory.ramOutputs circuit = [.InnerLayer 5 0, .InnerLayer 5 1] := by
  kernel_rfl

/-- Both RAM outputs are extension wires. -/
theorem outputRoles : isBase roles (.InnerLayer 5 0) = false ∧ isBase roles (.InnerLayer 5 1) = false := by
  decide +kernel

/-- The execute mask is a base wire. -/
theorem maskRole : isBase roles (.InnerLayer 4 0) = true := by
  decide +kernel

/-- The copy chain of the execute mask starts at a memory column. -/
theorem maskRoot : copyRoot circuit 4 (.InnerLayer 4 0) = .BaseLayerMemory 52 := by
  decide +kernel

/-- That memory column is the execute column of the placement. -/
theorem execute : memoryVariable circuit 52 = some Airbender.Blake2G.importedConstraintsDelegationColumns.execute := by
  decide +kernel

/-- The read tree reads the port read tuples and the issued request tuple. -/
theorem reads : tuplesMatch circuit ProductNative.BlakeGCached.native.registry ProductNative.BlakeGCached.native.memoryReadProduct.leaves
    (modelReadTuples Airbender.Blake2G.importedConstraintsMemoryPorts.toList 0x7C8 Airbender.Blake2G.importedConstraintsDelegationColumns.invocation) = true := by
  decide +kernel

/-- The write tree reads the port write tuples and the returned request tuple. -/
theorem writes : tuplesMatch circuit ProductNative.BlakeGCached.native.registry ProductNative.BlakeGCached.native.memoryWriteProduct.leaves
    (modelWriteTuples Airbender.Blake2G.importedConstraintsMemoryPorts.toList 0x7C8 Airbender.Blake2G.importedConstraintsDelegationColumns.invocation) = true := by
  decide +kernel

/-- Native base gates, extension caches and product gates give the RAM outputs from the model tokens. -/
theorem ram_products {R : Type} [CommRing R] (challenges : NativeMemory.Challenges R)
    (physical : GKRAddress → NativeArithmetic.F) (values : GKRAddress → R) (assignment : Nat → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds circuit physical)
    (placement : NativeArithmetic.PlacementAgreement circuit physical assignment)
    (extension : NativeMemory.Holds circuit challenges physical values) :
    NativeMemory.RamProducts circuit challenges values (assignment Airbender.Blake2G.importedConstraintsDelegationColumns.execute)
      (NativeMemory.standardReads (⟨.blakeG, assignment⟩ : Delegation.Row babyBearModulus))
      (NativeMemory.standardWrites (⟨.blakeG, assignment⟩ : Delegation.Row babyBearModulus)) := by
  have holds : ∀ gate ∈ ProductNative.BlakeGCached.native.gates,
      gate.Holds challenges.memory.embed (cacheChallenges challenges) (wires challenges roles physical values) := by
    rw [gates_binding]
    exact products_hold challenges roles physical values typed extension
  exact worker_ram_products challenges roles physical values assignment typed accepted extension placement outputs
    outputRoles maskRole maskRoot execute reads writes
    (ProductNative.BlakeGCached.native.memoryReadProductReduction _ _ _ holds)
    (ProductNative.BlakeGCached.native.memoryWriteProductReduction _ _ _ holds)

end Airbender.Compiler.WorkerPortsNative.BlakeGCached
