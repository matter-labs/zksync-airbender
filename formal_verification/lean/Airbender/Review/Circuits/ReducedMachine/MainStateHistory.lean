import Airbender.Review.Circuits.ReducedMachine.TokenLedger
import Airbender.Review.Helpers.Context.ReducedMachine

namespace Airbender.NativeMainStateHistory
open NativeTokenLedger Trace Airbender.ReducedMachine.NativeMainAuxiliary
open Airbender.ReducedMachine.NativeMemoryBoundary

def selectAssignments (assignments : List (Nat → F)) : List (Nat → F) :=
  assignments.filter fun w => w Airbender.ReducedMachine.Native.importedConstraintsTraceColumns.execute = 1

/-- Select actual execute1 observations from ALL ordinary physical main rows.
    No instruction-profile, caller-request or worker filter is introduced. -/
def rows {R : Type} [Field R] (mains : List (MainProof R)) : List (Row mersenne31Modulus NativeReducedFamily) :=
  (selectAssignments (mainRows mains)).map fun w => ⟨.reduced,w⟩

/-- Both PC and timestamp field limbs are retained, without word/range answers. -/
def state (key : PCKey) : PCState.State mersenne31Modulus :=
  ⟨(key.pc[0],key.pc[1]),(key.time[0],key.time[1])⟩

def Path {R : Type} [Field R] (mains : List (MainProof R)) (inputs : PublicBoundary)
    (path : List (PCState.State mersenne31Modulus)) : Prop :=
  path.head? = some (state initialPCKey) ∧ path.getLast? = some (state (finalPCKey inputs)) ∧
    (path.zip path.tail).Perm ((rows mains).map fun row => (row.start,row.finish)) ∧
    (path.map fun point => (timeOfPair point.timestamp).value).Nodup

/-- Actual three main write slots, including both readonly timestamp refreshes. -/
def writeTimes {R : Type} [Field R] (mains : List (MainProof R)) : List Nat :=
  (rows mains).flatMap fun row => row.ports.toList.map fun port => row.clock+port.clock.offset

/-- Chronology of actual active MAIN states, derived from complete body and the
    explicit full native logical ledger. No Sail instruction/CSR/MOP semantics,
    initialized worker memory or request issuance/fulfillment is asserted. -/
structure Effects {R : Type} [Field R] (mains : List (MainProof R)) (inputs : PublicBoundary) : Prop where
  states : (state initialPCKey :: (rows mains).map Row.finish).Perm
    (state (finalPCKey inputs) :: (rows mains).map Row.start)
  clocks : ∀ row ∈ rows mains,
    (decodeTimestamp row.assignment row.columns.initialTime).Bounded ∧
      (decodeTimestamp row.assignment row.columns.initialTime).lo % 4 = 0
  finalClocks : ∀ row ∈ rows mains, (decodeTimestamp row.assignment row.columns.finalTime).Bounded
  terminalBound : (timeOfPair (state (finalPCKey inputs)).timestamp).Bounded
  advances : ∀ row ∈ rows mains,
    (decodeTimestamp row.assignment row.columns.finalTime).value =
      (decodeTimestamp row.assignment row.columns.initialTime).value+4
  interval : ∀ row ∈ rows mains,
    4 ≤ (timeOfPair row.start.timestamp).value ∧
      (timeOfPair row.start.timestamp).value+4 ≤ (timeOfPair (state (finalPCKey inputs)).timestamp).value
  unique : ((rows mains).map fun row => (decodeTimestamp row.assignment row.columns.initialTime).value).Nodup
  writes : ∀ row ∈ rows mains, ∀ port ∈ row.ports,
    (timeOfPair (writeToken row.columns row.assignment port).time).Bounded ∧
      (timeOfPair (writeToken row.columns row.assignment port).time).value = row.clock+port.clock.offset
  writesUnique : (writeTimes mains).Nodup
  terminal : (timeOfPair (state (finalPCKey inputs)).timestamp).value = 4+4*(rows mains).length
  path : ∃ path, Path mains inputs path

end Airbender.NativeMainStateHistory
