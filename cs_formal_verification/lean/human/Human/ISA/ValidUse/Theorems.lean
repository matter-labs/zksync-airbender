module
public import Human.ISA.ValidUse.Model

@[expose] public section
namespace RV.ValidUse
open Spec

/-- On valid bigint inputs, the delegation effect is the reference u256 operation. -/
def BigintReferenceClaim : Prop :=
  ∀ state, Bigint state → Delegation.effect .bigint (state.getReg 10) (state.getReg 11) (state.getReg 12)
    state.delegationRAM = bigintReference state

/-- A complete valid G schedule equals the independent BLAKE2s round function. -/
def GReferenceClaim : Prop :=
  ∀ reduced state left right, G reduced state left right →
    ∃ finish, calls (.replicate (if reduced then 56 else 80) .blakeG) state = some finish ∧
      ChangesOnly state finish left 64 12 ∧ finish.getReg 12 = (if reduced then 0x80#32 else 0#32) ∧
      readWords finish.mem left 16 = gReference reduced (readWords state.mem left 16) (readWords state.mem right 16)

/-- A complete valid round schedule equals BLAKE2s compression. -/
def RoundReferenceClaim : Prop :=
  ∀ reduced state left right counter last, Round reduced state left right counter last →
    ∃ finish, calls (.replicate (if reduced then 7 else 10) .blakeRound) state = some finish ∧
      ChangesOnly state finish left 96 12 ∧
      readWords finish.mem left 8 = compressRounds (if reduced then 7 else 10)
        (readWords state.mem left 8) (readWords state.mem right 16) counter last

/-- A complete valid compression-mode schedule equals the BLAKE2s two-to-one hash. -/
def HashReferenceClaim : Prop :=
  ∀ reduced right state left sibling, Hash reduced right state left sibling →
    ∃ finish, calls (.replicate (if reduced then 7 else 10) .blakeRound) state = some finish ∧
      ChangesOnly state finish left 96 12 ∧
      readWords finish.mem left 8 = compressRounds (if reduced then 7 else 10) (Vector.ofFn configuredIV)
        (if right then readWords state.mem sibling 8 ++ readWords state.mem left 8
          else readWords state.mem left 8 ++ readWords state.mem sibling 8) 64#32 true

/-- A complete valid split Keccak schedule equals Keccak-f[1600]. -/
def SplitKeccakReferenceClaim : Prop :=
  ∀ state pointer, Keccak state pointer →
    ∃ finish, calls f1600Calls state = some finish ∧ ChangesOnly state finish pointer 248 10 ∧
      readLanes finish.mem pointer 25 = keccakF (readLanes state.mem pointer 25)

/-- A complete valid special5 schedule equals Keccak-f[1600]. -/
def Special5ReferenceClaim : Prop :=
  ∀ state pointer, Keccak state pointer →
    ∃ finish, calls (.replicate 649 .keccak) state = some finish ∧ ChangesOnly state finish pointer 248 10 ∧
      readLanes finish.mem pointer 25 = keccakF (readLanes state.mem pointer 25)

end RV.ValidUse

namespace RV.ValidUse

/-- The valid reference-use assumptions have a concrete state and RAM buffers. -/
def BigintReferenceSatisfiableClaim : Prop :=
  ∃ state : State, Bigint state

/-- The valid reference-use assumptions have a concrete state and RAM buffers. -/
def GReferenceSatisfiableClaim : Prop :=
  ∃ (reduced : Bool) (state : State) (left right : Word), G reduced state left right

/-- The valid reference-use assumptions have a concrete state and RAM buffers. -/
def RoundReferenceSatisfiableClaim : Prop :=
  ∃ (reduced : Bool) (state : State) (left right counter : Word) (last : Bool), Round reduced state left right counter last

/-- The valid reference-use assumptions have a concrete state and RAM buffers. -/
def HashReferenceSatisfiableClaim : Prop :=
  ∃ (reduced right : Bool) (state : State) (left sibling : Word), Hash reduced right state left sibling

/-- The valid reference-use assumptions have a concrete state and RAM buffers. -/
def SplitKeccakReferenceSatisfiableClaim : Prop :=
  ∃ (state : State) (pointer : Word), Keccak state pointer

/-- The valid reference-use assumptions have a concrete state and RAM buffers. -/
def Special5ReferenceSatisfiableClaim : Prop :=
  ∃ (state : State) (pointer : Word), Keccak state pointer

end RV.ValidUse
