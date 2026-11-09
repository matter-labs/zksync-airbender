import Airbender.Review.Trace.Families.ReducedMachine.WorkerSnapshot

namespace Airbender.NativeWorkerPointers
open Airbender.Blake2Worker.Native Airbender.ReducedMachine.Native
abbrev F := ZMod mersenne31Modulus

/-- The two ACTUAL readonly ABI pointer GPR ports, x10 then x11. -/
def pointerSlot (pointer : Fin 2) : Fin 43 := if pointer = 0 then 0 else 25

/-- Actual value-changing third MAIN write on the SAME initialized token path.
    The full encoded value and BOTH raw time fields remain. This is an observed
    origin, not an expected pointer/history or CSR/Sail issuance assumption. -/
def MainOrigin {Setup R : Type} [Field R]
    (proofs : List (Airbender.NativeInitializationBatch.Proof R)) (workers : WorkerBatch Setup R)
    (token : Airbender.NativeMixedMemoryOrder.Token) : Prop :=
  ∃ row ∈ Airbender.NativeMixedMemoryOrder.mainRows proofs, ∃ port ∈ row.ports,
    row.assignment importedConstraintsTraceColumns.execute = 1 ∧
    port = Airbender.ReducedMachine.NativeMainAuxiliary.mainPort 2 ∧
    (Trace.writeToken row.columns row.assignment port).address = token.address ∧
    (Trace.writeToken row.columns row.assignment port).value = token.value ∧
    (Trace.writeToken row.columns row.assignment port).value ≠ (Trace.readToken row.assignment port).value ∧
    Relation.ReflTransGen (Airbender.NativeMixedMemoryOrder.Step proofs workers)
      (Trace.writeToken row.columns row.assignment port) token

end Airbender.NativeWorkerPointers
