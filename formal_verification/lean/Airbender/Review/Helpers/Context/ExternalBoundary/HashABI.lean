import Airbender.Review.Trace.Workers.Blake2G.Call
import Airbender.Review.Trace.Workers.Blake2Round.Call
import Airbender.Review.Trace.Workers.Keccak.Call

namespace Airbender.ExternalBoundary.HashABI
open Arithmetic Trace

/-- Temporary input restriction: the actual x12 read is one of the 80 full or
56 reduced G micro-call controls. This proof does not derive the restriction
from native acceptance. -/
def GControl (w : Nat → ZMod p) : Prop :=
  ∃ reduced : Bool, ∃ index : Fin (Blake2G.callCount reduced),
    (readToken w Blake2G.importedConstraintsMemoryPorts[8]).word =
      Blake2G.controlAt reduced index.val

/-- Temporary separation of the actual G state/message base pointers. This is
an additional input condition; it is not derived here from native acceptance. -/
def GBases (w : Nat → ZMod p) : Prop :=
  (Blake2G.Native.statePointer w).toBitVec ≠ (Blake2G.Native.messagePointer w).toBitVec

/-- Temporary extended-round reference profile: the actual x12 word has a zero
low limb, three flags and exactly one round bit, below seven or ten according
to the reduced flag. The zero low limb is a restriction of this proof's existing
reference profile; it is not asserted to be required by the Rust VM.
The execution theorem takes this condition as an assumption. -/
def RoundControl (w : Nat → ZMod p) : Prop :=
  ∃ flags : Fin 8, ∃ index : Fin 10,
    index.val < (if flags.val % 2 = 1 then 7 else 10) ∧
    (readToken w Blake2Round.importedConstraintsMemoryPorts[42]).word =
      Blake2Round.controlAt flags index.val

/-- Temporary Keccak reference profile: the actual x10 word is a control from
the existing 649-micro-call protocol, including the final round-24 Iota.
This restricts inputs only: it supplies no execution, outputs, occurrence plan,
call count or proof that a complete permutation took place. -/
def KeccakControl (w : Nat → ZMod p) : Prop :=
  ∃ index : Fin 649,
    (readToken w Keccak.importedConstraintsMemoryPorts[0]).word =
      ⟨(Keccak.scheduleControl ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩).packed, 0⟩

end Airbender.ExternalBoundary.HashABI
