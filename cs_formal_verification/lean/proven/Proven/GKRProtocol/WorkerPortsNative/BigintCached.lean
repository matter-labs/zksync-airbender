module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.NativeMemoryWorkers
public import Proven.GKRProtocol.ProductNative.BigintCached
public import Proven.KernelRfl
public import Human.Compiler.WorkerMemoryPorts

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.WorkerPortsNative.BigintCached
open Airbender Airbender.Compiler NativeMemoryBridge
set_option maxRecDepth 32768

/-- The cached capture. -/
noncomputable abbrev circuit : Circuit := Captures.Bigint.imported.circuit

/-- Base-field caches and gates of the capture write its base-field wires. -/
noncomputable abbrev roles : GKRAddress → Bool := structuralRoles circuit

/-- The imported product gates are the RAM-product recipes of the imported capture. -/
theorem gates_binding : ProductNative.BigintCached.native.gates = productGates circuit := by
  kernel_rfl

/-- Every recipe reads its operands with the structural field roles. -/
theorem typed : typingChecked roles circuit = true := by
  decide +kernel

/-- The RAM output map of the capture. -/
theorem outputs : NativeMemory.ramOutputs circuit = [.InnerLayer 6 0, .InnerLayer 6 1] := by
  kernel_rfl

/-- Both RAM outputs are extension wires. -/
theorem outputRoles : isBase roles (.InnerLayer 6 0) = false ∧ isBase roles (.InnerLayer 6 1) = false := by
  decide +kernel

/-- The execute mask is a base wire. -/
theorem maskRole : isBase roles (.InnerLayer 5 0) = true := by
  decide +kernel

/-- The copy chain of the execute mask starts at a memory column. -/
theorem maskRoot : copyRoot circuit 5 (.InnerLayer 5 0) = .BaseLayerMemory 94 := by
  decide +kernel

/-- That memory column is the execute column of the placement. -/
theorem execute : memoryVariable circuit 94 = some Airbender.Bigint.importedConstraintsDelegationColumns.execute := by
  decide +kernel

/-- The read tree reads the port read tuples and the issued request tuple. -/
theorem reads : tuplesMatch circuit ProductNative.BigintCached.native.registry ProductNative.BigintCached.native.memoryReadProduct.leaves
    (modelReadTuples Airbender.Bigint.importedConstraintsMemoryPorts.toList 0x7CA Airbender.Bigint.importedConstraintsDelegationColumns.invocation) = true := by
  decide +kernel

/-- The write tree reads the port write tuples and the returned request tuple. -/
theorem writes : tuplesMatch circuit ProductNative.BigintCached.native.registry ProductNative.BigintCached.native.memoryWriteProduct.leaves
    (modelWriteTuples Airbender.Bigint.importedConstraintsMemoryPorts.toList 0x7CA Airbender.Bigint.importedConstraintsDelegationColumns.invocation) = true := by
  decide +kernel

/-- Native base gates, extension caches and product gates give the RAM outputs from the model tokens. -/
theorem ram_products {R : Type} [CommRing R] (challenges : NativeMemory.Challenges R)
    (physical : GKRAddress → NativeArithmetic.F) (values : GKRAddress → R) (assignment : Nat → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds circuit physical)
    (placement : NativeArithmetic.PlacementAgreement circuit physical assignment)
    (extension : NativeMemory.Holds circuit challenges physical values) :
    NativeMemory.RamProducts circuit challenges values (assignment Airbender.Bigint.importedConstraintsDelegationColumns.execute)
      (NativeMemory.standardReads (⟨.bigint, assignment⟩ : Delegation.Row babyBearModulus))
      (NativeMemory.standardWrites (⟨.bigint, assignment⟩ : Delegation.Row babyBearModulus)) := by
  have holds : ∀ gate ∈ ProductNative.BigintCached.native.gates,
      gate.Holds challenges.memory.embed (cacheChallenges challenges) (wires challenges roles physical values) := by
    rw [gates_binding]
    exact products_hold challenges roles physical values typed extension
  exact worker_ram_products challenges roles physical values assignment typed accepted extension placement outputs
    outputRoles maskRole maskRoot execute reads writes
    (ProductNative.BigintCached.native.memoryReadProductReduction _ _ _ holds)
    (ProductNative.BigintCached.native.memoryWriteProductReduction _ _ _ holds)

end Airbender.Compiler.WorkerPortsNative.BigintCached
