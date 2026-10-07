import Airbender.Review.Blake2G.Model

namespace Airbender.Blake2G.Control

/- Symbolic controller-table reconstruction, not extracted setup data. Sources:
   cs/src/tables/blake_g_function_precompile_related.rs;
   blake2s_u32/src/lib.rs::SIGMAS;
   riscv_transpiler/src/vm/delegations/blake2_g_function.rs::MIXING_FUNCTION_ACCESS_IDXES.
   This describes a single table row, not a complete delegation run. -/

def stateLanes : Vector (Vector Nat 4) 8 := #v[
  #v[0, 4, 8, 12], #v[1, 5, 9, 13], #v[2, 6, 10, 14], #v[3, 7, 11, 15],
  #v[0, 5, 10, 15], #v[1, 6, 11, 12], #v[2, 7, 8, 13], #v[3, 4, 9, 14]]

def messageSchedule : Vector (Vector Nat 16) 10 := #v[
  #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
  #v[14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
  #v[11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
  #v[7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
  #v[9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
  #v[2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
  #v[12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
  #v[13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
  #v[6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
  #v[10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0]]

structure Input where
  register : Fin 256
  active : Bool

structure Output where
  register : Arithmetic.Word
  stateOffsets : Vector Nat 4
  messageOffsets : Vector Nat 2
  deriving DecidableEq

def Input.key (input : Input) : Fin 512 :=
  ⟨input.register.val + if input.active then 256 else 0, by
    have bound := input.register.isLt
    cases input.active <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega⟩

/-- Active rows increment the seven-bit counter, wrapping after 56 or 80 calls.
    Out-of-schedule counters select call zero and reset, matching Rust's fallback.
    Inactive rows clear all seven outputs. Indices are in words, not bytes. -/
def step (input : Input) : Output :=
  if !input.active then ⟨⟨0, 0⟩, Vector.replicate 4 0, Vector.replicate 2 0⟩ else
    let mode := input.register.val / 128
    let counter := input.register.val % 128
    let limit := if mode = 0 then 80 else 56
    let call : Fin 80 := ⟨if counter < limit then counter else 0, by
      dsimp [limit]
      split_ifs <;> omega⟩
    let round : Fin 10 := ⟨call.val / 8, by have := call.isLt; omega⟩
    let mixing : Fin 8 := ⟨call.val % 8, Nat.mod_lt _ (by decide)⟩
    let next := if counter + 1 < limit then counter + 1 else 0
    ⟨⟨mode * 128 + next, 0⟩, stateLanes[mixing],
      #v[messageSchedule[round][2 * mixing.val], messageSchedule[round][2 * mixing.val + 1]]⟩

def Output.row (output : Output) : Vector Nat 7 :=
  #v[output.register.lo, output.stateOffsets[0], output.stateOffsets[1],
    output.stateOffsets[2], output.stateOffsets[3], output.messageOffsets[0], output.messageOffsets[1]]

def controllerRows (key : Fin 512) : Vector Nat 7 :=
  (step ⟨⟨key.val % 256, Nat.mod_lt _ (by decide)⟩, decide (256 ≤ key.val)⟩).row

def spec (input : Input) (output : Output) : Prop := output = step input

/-- Canonical decoding of the control register and the six imported offset columns.
    Input's eight-bit type is the ABI input bound; memory transport supplies it. -/
structure Mapping {p : Nat} (input : Input) (output : Output) (w : Nat → ZMod p) : Prop where
  inputRegister : input.register.val = (w Variables.controlReadLo).val
  execute : w Variables.execute = if input.active then 1 else 0
  outputs : output = ⟨⟨(w Variables.controlWriteLo).val, (w Variables.controlWriteHi).val⟩,
    Variables.stateOffsetColumns.map (fun column => (w column).val),
    Variables.messageOffsetColumns.map (fun column => (w column).val)⟩

def circuitModel {p : Nat} [Fact p.Prime] :
    Verification.CircuitModel Input Output (Nat → ZMod p) where
  satisfies := fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w)
    (importedConstraints (setupTable controllerRows))
  represents := Mapping

end Airbender.Blake2G.Control
