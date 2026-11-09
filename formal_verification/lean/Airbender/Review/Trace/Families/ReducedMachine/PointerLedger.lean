import Airbender.Review.Trace.Families.ReducedMachine.PointerPrefix

namespace Airbender.NativePointerLedger
open Airbender.Blake2Worker.Native Airbender.NativeMemoryTokens
open Airbender.ReducedMachine.NativeMemoryBoundary Airbender.ReducedMachine.NativeMainAuxiliary
abbrev F := ZMod mersenne31Modulus

/-- Every position in the finite41-row active prefix, in source order.
    This does not remove rows from any full native acceptance relation. -/
def rowsList (activeRows : Fin 41 → Nat → F) : List (Nat → F) :=
  (List.finRange 41).map activeRows

/-- Actual ALL32 GPR seeds and ALL three ports per prefix row, retaining raw
    timestamp limbs and readonly refreshes. The endpoint is BEFORE a worker,
    not a whole verifier boundary or a premise of global source acceptance. -/
def MemoryBalanced (activeRows : Fin 41 → Nat → F) : Prop :=
  (NativeInitializationSeedBoundary.initialRegisters ++
    (rowsList activeRows).flatMap (fun w => mainTokens w true)).Perm
  (NativeInitializationSeedBoundary.finalRegisters NativePointerPrefix.prefixEndpoint ++
    (rowsList activeRows).flatMap (fun w => mainTokens w false))

/-- Actual incoming/outgoing PC and both timestamp fields at every prefix row.
    No original instruction fetch, Sail, transcript or final protocol claim. -/
def PCBalanced (activeRows : Fin 41 → Nat → F) : Prop :=
  (initialPCKey :: (rowsList activeRows).map (fun w => mainPCKey w true)).Perm
  (finalPCKey NativePointerPrefix.prefixEndpoint ::
    (rowsList activeRows).map (fun w => mainPCKey w false))

def Balanced (activeRows : Fin 41 → Nat → F) : Prop :=
  MemoryBalanced activeRows ∧ PCBalanced activeRows
end Airbender.NativePointerLedger
