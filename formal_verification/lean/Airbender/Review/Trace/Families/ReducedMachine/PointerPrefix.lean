import Airbender.Review.Circuits.ReducedMachine.InitializationBoundary
import Airbender.Review.Circuits.ReducedMachine.InitializationSeedBoundary
import Airbender.Review.Circuits.ReducedMachine.DelegationSupport

namespace Airbender.NativePointerPrefix
open Airbender.ReducedMachine.Native Airbender.Blake2Worker.Native
abbrev F := ZMod mersenne31Modulus

/-- Keep every ordinary position. The concrete41-row prefix ends at N-2;
    N-1 remains reserved, and all earlier ordinary positions remain present. -/
def blockStart : Nat := callerAuxiliaryLayout.traceLength - 42

def place (activeRows : Fin 41 → Nat → F) (idle : Nat → F) (i : Nat) : Nat → F :=
  if h : blockStart ≤ i ∧ i < blockStart + 41 then
    activeRows ⟨i - blockStart,by omega⟩ else idle

/-- Actual state24/message16 RAM byte addresses for this candidate. -/
def ramAddress (index : Nat) : Nat := if index < 24 then 4 * index else 128 + 4 * (index - 24)

/-- Constructed GPR/PC endpoint of the finite MAIN prefix, BEFORE the worker.
    This is not the final full verifier/worker public-register boundary. -/
def prefixEndpoint : Airbender.ReducedMachine.NativeMemoryBoundary.PublicBoundary :=
  ⟨(fun index => ⟨if index.val = 11 then 128 else 0,
    #v[if index.val = 0 then 166 else if index.val = 11 then 162 else 0,0]⟩),164,#v[168,0]⟩

/-- Native BODY/initialization components on one shared row family. This records
    conclusions for the constructed candidate; it does not replace SourceAccepted
    or assert memory auxiliaries, scalar/table families, fetched program, workers,
    global matching, physical extraction or a final verifier boundary. -/
structure Components (activeRows : Fin 41 → Nat → F) (idle : Nat → F) : Prop where
  body : ∀ i < callerAuxiliaryLayout.traceLength - 1,
    FlatOperation.ConstraintsHoldFlat
      (Verification.environment (place activeRows idle i))
      (ReducedMachine.Native.importedConstraints ReducedMachine.NativeRuntimePool.table)
  active : ∀ row, activeRows row importedConstraintsTraceColumns.execute = 1
  ordering : ∀ i < callerAuxiliaryLayout.traceLength - 2,
    NativeInitializationOrdering.AdjacentAccepted
      (place activeRows idle i) (place activeRows idle (i + 1))
  records : ∀ index : Fin 40,
    NativeInitializationBoundary.record (activeRows ⟨index.val + 1,by have := index.isLt; omega⟩) =
      #v[(ramAddress index.val : F),0,0,0,167,0]
  nonpadding : ∀ index : Fin 40,
    NativeInitializationLedger.paddingRow (activeRows ⟨index.val + 1,by have := index.isLt; omega⟩) = false
  first : NativeInitializationBoundary.record (place activeRows idle 0) = #v[0,0,0,0,0,0]
  last : NativeInitializationBoundary.record
    (place activeRows idle (callerAuxiliaryLayout.traceLength - 2)) = #v[188,0,0,0,167,0]
  endpoints : NativeInitializationBoundary.EndpointAccepted
      (place activeRows idle 0) #v[0,0,0,0,0,0] ∧
    NativeInitializationBoundary.EndpointAccepted
      (place activeRows idle (callerAuxiliaryLayout.traceLength - 2)) #v[188,0,0,0,167,0]
  pointer : (ReducedMachine.NativeMainAuxiliary.mainMemoryKey (activeRows 0) 2 true).address = ⟨1,11,0⟩ ∧
    (ReducedMachine.NativeMainAuxiliary.mainMemoryKey (activeRows 0) 2 true).value = #v[128,0] ∧
    (ReducedMachine.NativeMainAuxiliary.mainMemoryKey (activeRows 0) 2 true).time = #v[6,0]
  request : csrRequest (activeRows 40) = ⟨1,1991,some 0,3⟩ ∧
    NativeDelegationSupport.callerKey (activeRows 40) = ⟨1991,0,167,0⟩
end Airbender.NativePointerPrefix
