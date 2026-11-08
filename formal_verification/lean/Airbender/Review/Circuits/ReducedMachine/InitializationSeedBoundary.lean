import Airbender.Review.Circuits.ReducedMachine.InitializationSeedDomain
import Airbender.Review.Helpers.Memory.ReducedMachineShadowImage

namespace Airbender.NativeInitializationSeedBoundary
open Airbender.NativeInitializationBatch (Proof mainProofs)
open Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native
abbrev F := ZMod mersenne31Modulus

def registerCells : List Trace.Cell :=
  (List.finRange 32).map fun index => Trace.Cell.register (BitVec.ofNat 5 index.val)

def initialRegisters : List (Trace.MemoryToken mersenne31Modulus) :=
  (List.finRange 32).map fun index => Airbender.NativeMemoryTokens.encodeKey (registerInitialKey index)

def finalRegisters (inputs : PublicBoundary) : List (Trace.MemoryToken mersenne31Modulus) :=
  (List.finRange 32).map fun index => Airbender.NativeMemoryTokens.encodeKey (registerFinalKey inputs index)

/-- ALL32 actual public GPR seeds, including x0, plus actual nonpadding RAM seeds. -/
def initialTokens {R : Type} [Field R] (proofs : List (Proof R)) :=
  initialRegisters ++ Airbender.NativeInitializationSeedDomain.tokens proofs true

def terminalTokens {R : Type} [Field R] (proofs : List (Proof R)) (inputs : PublicBoundary) :=
  finalRegisters inputs ++ Airbender.NativeInitializationSeedDomain.tokens proofs false

def cells {R : Type} [Field R] (proofs : List (Proof R)) :=
  registerCells ++ Airbender.NativeInitializationSeedDomain.cells proofs

/-- The actual three active main memory ports and ALL43 worker ports, including
    inactive worker observations. This filters no caller request or worker row. -/
def accessTokens {Setup R : Type} [Field R] (proofs : List (Proof R)) (batch : WorkerBatch Setup R) (write : Bool) :=
  ((Airbender.NativeMainStateHistory.selectAssignments (Airbender.NativeTokenLedger.mainRows (mainProofs proofs))).flatMap
    fun w => Airbender.NativeMemoryTokens.mainTokens w write) ++
    ((Airbender.NativeTokenLedger.workerRows batch).flatMap fun w => Airbender.NativeMemoryTokens.workerTokens w write)

def architecturalCells (domain : List Trace.Cell) :=
  domain.filter fun c => Airbender.ReducedMachine.NativeShadow.architecturalAddress c.addressCode

def shadowSeed : Trace.Cell → Option Airbender.ReducedMachine.NativeShadow.ShadowSeed
  | .register _ => none
  | .ram address => if address.toNat < 4194304 then some (address,0) else none

def shadowSeeds (domain : List Trace.Cell) := domain.filterMap shadowSeed

/-- Complete observed logical seed boundary and exact ROM-shadow partition.
    This is not successful original Sail image reads, independent public-domain
    coverage, alignment/platform scope or an initialized combined memory history. -/
structure Effects {R : Type} [Field R] (proofs : List (Proof R)) : Prop where
  domain : (cells proofs).Nodup
  encoding : initialTokens proofs = (cells proofs).map (fun c => c.initialToken (p := mersenne31Modulus) 0)
  addresses : ((initialTokens proofs).map Trace.MemoryToken.address).Nodup
  clocks : ∀ token ∈ initialTokens proofs, token.time = (0,0)
  partition : (initialTokens proofs).Perm
    (((architecturalCells (cells proofs)).map fun c => c.initialToken (p := mersenne31Modulus) 0) ++
      Airbender.ReducedMachine.NativeShadow.shadowTokens (shadowSeeds (cells proofs)))
  partitionDomain : (architecturalCells (cells proofs) ++ (shadowSeeds (cells proofs)).map (fun seed => Trace.Cell.ram seed.1)).Nodup
  architectural : ∀ c ∈ architecturalCells (cells proofs), Airbender.ReducedMachine.NativeShadow.architecturalAddress c.addressCode = true
  shadows : ∀ seed ∈ shadowSeeds (cells proofs), seed.1.toNat < 4194304 ∧ seed.2 = 0

end Airbender.NativeInitializationSeedBoundary
