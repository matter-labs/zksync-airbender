import Airbender.Review.Circuits.Blake2G.Protocol
import Airbender.Review.Circuits.Blake2G.Execution
import Airbender.Review.Circuits.Blake2Round.Protocol
import Airbender.Review.Circuits.Keccak.Protocol

namespace Airbender.ExternalBoundary.HashABI
open Arithmetic Trace

/-- Lower-level private-witness restriction: the actual x12 read is one of the 80 full or
56 reduced G micro-call controls. This proof does not derive the restriction
from native acceptance. It permits interior positions; VM invocation entry
requires counter zero, which is a separate bundle condition. -/
def GControl (w : Nat → ZMod p) : Prop :=
  ∃ reduced : Bool, ∃ index : Fin (Blake2G.callCount reduced),
    (readToken w Blake2G.importedConstraintsMemoryPorts[8]).word =
      Blake2G.controlAt reduced index.val

/-- Separation of the actual G state/message base pointers. This is
an additional private-witness condition; it is not derived here from native acceptance. -/
def GBases (w : Nat → ZMod p) : Prop :=
  (Blake2G.Native.statePointer w).toBitVec ≠ (Blake2G.Native.messagePointer w).toBitVec

/-- Extended-round supported-use mask: the actual x12 word has a zero
low limb, three flags and exactly one round bit, below seven or ten according
to the reduced flag. The zero low limb is part of the blessed callers' mask
rule; it is not asserted to be required by the Rust VM for arbitrary calls.
The execution theorem takes this private-witness condition as an assumption.
It permits interior round positions; VM bundle entry requires round zero. -/
def RoundControl (w : Nat → ZMod p) : Prop :=
  ∃ flags : Fin 8, ∃ index : Fin 10,
    index.val < (if flags.val % 2 = 1 then 7 else 10) ∧
    (readToken w Blake2Round.importedConstraintsMemoryPorts[42]).word =
      Blake2Round.controlAt flags index.val

/-- Conditional special5 protocol domain: the actual x10 word is a control from
the existing 649-micro-call protocol, including the final round-24 Iota.
This restricts the private witness: it supplies no execution, outputs, occurrence plan,
call count or proof that a complete permutation took place. -/
def KeccakControl (w : Nat → ZMod p) : Prop :=
  ∃ index : Fin 649,
    (readToken w Keccak.importedConstraintsMemoryPorts[0]).word =
      ⟨(Keccak.scheduleControl ⟨index.val, Nat.lt_trans index.isLt (by decide)⟩).packed, 0⟩

end Airbender.ExternalBoundary.HashABI
