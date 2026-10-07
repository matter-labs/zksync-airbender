import Airbender.Review.Blake2Round.Preparation
import Airbender.Review.Blake2Round.Tables

namespace Airbender.Blake2Round.Mixing

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

structure Input where
  state : Vector Arithmetic.Word 16
  message : Vector Arithmetic.Word 16

abbrev Output := Vector Arithmetic.Word 16

/-- The eight mixing calls use Clean's existing round function. Message words
    are already SIGMA-selected; preparation and scheduling have separate claims. -/
def spec (input : Input) (output : Output) : Prop :=
  output.map Arithmetic.Word.value =
    Specs.BLAKE3.round (input.state.map Arithmetic.Word.value)
      (input.message.map Arithmetic.Word.value)

def extendedWrites : Vector (Nat × Nat) 16 :=
  Vector.ofFn fun i => (39 + 4 * i.val, 40 + 4 * i.val)

structure WordMapping {p : Nat} (input : Input) (output : Output)
    (w : Nat → ZMod p) : Prop where
  state : input.state = Preparation.words w Variables.preparedState
  message : input.message = Preparation.words w Variables.scheduledMessage
  output : output = Preparation.words w extendedWrites

/-- G lookups range the other input lanes and every intermediate/output.
    Bounds on the selected messages and eight addition inputs remain external. -/
structure InterfaceAssumptions {p : Nat} (input : Input) (_output : Output)
    (_w : Nat → ZMod p) : Prop where
  additionInputs : ∀ i : Fin 4, input.state[i.val].Bounded ∧ input.state[8 + i.val].Bounded
  messages : ∀ i : Fin 16, input.message[i].Bounded

def circuitModel {p : Nat} [Fact p.Prime] :
    Verification.CircuitModel Input Output (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat
    (Verification.environment w) (importedConstraints setupTable)
  represents := WordMapping

/-- The output projection follows the imported memory-port labels. This
    checks numbering; global memory transport remains an interface. -/
theorem output_roles : ∀ i : Fin 16,
    importedConstraintsVariableNames.lookup extendedWrites[i].1 =
      some s!"state read/write from x10 indirect access {8 + i.val} write[0]" ∧
    importedConstraintsVariableNames.lookup extendedWrites[i].2 =
      some s!"state read/write from x10 indirect access {8 + i.val} write[1]" := by
  intro i
  fin_cases i <;> decide

end Airbender.Blake2Round.Mixing
