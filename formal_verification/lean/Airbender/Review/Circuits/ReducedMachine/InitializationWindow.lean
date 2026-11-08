import Airbender.Review.Circuits.ReducedMachine.InitializationBoundary

namespace Airbender.NativeInitializationWindow
open Airbender.NativeInitializationBoundary Airbender.NativeInitializationOrdering

/-- Pure source reference for successful checked-u16 parsing: canonical field
    representatives, BOTH actual high-bit masks, 32-bit shift and bitwise OR.
    This is not Rust/field-storage/serialization/compiler refinement. -/
def parseAddress (values : Vector F 6) : Option (BitVec 32) :=
  let low := BitVec.ofNat 32 values[0].val
  let high := BitVec.ofNat 32 values[1].val
  if low &&& 0xffff0000 = 0 ∧ high &&& 0xffff0000 = 0 then
    some (low ||| (high <<< 16)) else none

/-- Actual successful native window check. The ELSE branch retains zero address
    and ALL four teardown fields of the previous terminal. Empty/padded chunks
    are not required to have a strictly increasing public window. -/
def WindowAccepted (previous current : PublicValues) : Prop :=
  match parseAddress previous.oneBeforeLast,parseAddress current.first with
  | some last,some first =>
    if last.toNat < first.toNat then True else
      last.toNat = 0 ∧ ∀ slot : Fin 4, previous.oneBeforeLast[slot.val+2] = 0
  | _,_ => False

/-- Observed complete main/scalar proof and its public boundary inputs. -/
structure Chunk (R : Type) [Field R] where
  proof : Airbender.NativeScalar16Arguments.Proof R
  values : PublicValues

/-- Indexed finite source-normalized batch. EVERY supplied chunk and EVERY
    adjacent native window is checked; this is not full Rust ProofOutput/count/
    setup-cap/challenge/transcript/global-memory/delegation acceptance. No expected
    row/seed/request/worker stream or result/order is a premise. -/
structure Accepted {R : Type} [Field R] (embed : F →+* R)
    (memory : Airbender.Blake2Worker.Native.MemoryKeyChallenges R)
    (pc : Airbender.ReducedMachine.NativeMemoryBoundary.PCChallenges R) (gamma : R)
    (count : Nat) (chunks : Nat → Chunk R) : Prop where
  components : ∀ c < count, Airbender.NativeInitializationBoundary.Accepted embed memory pc gamma (chunks c).proof (chunks c).values
  windows : ∀ c, c + 1 < count → WindowAccepted (chunks c).values (chunks (c + 1)).values

end Airbender.NativeInitializationWindow
