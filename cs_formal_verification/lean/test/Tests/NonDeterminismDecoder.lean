module
public import Slop.Trace.ROMView
public import Slop.AddSub.Selectors
public import Slop.Trace.Pooled
public import Human.Helpers.Decoder.PooledExternalInput
public import Human.Circuits.WordMemory.Output
public import Human.Helpers.Core.BabyBearPrime
public import Slop.Trace.CompositionCore
public import Slop.Trace.Family.Values
public import Human.Circuits.JumpBranchSlt.Jump
public import Human.Circuits.SubwordMemory.Output
public import Slop.JumpBranchSlt.Branch
public import Slop.JumpBranchSlt.Jump
public import Slop.MulDiv.Product
public import Human.Circuits.MulDiv.Operation
public import Slop.MulDiv.Values
public import Slop.ShiftBinop.Ports
public import Slop.SubwordMemory.Values
public import Slop.Defs.Helpers.Decoder.PooledExternalInput
public import Slop.Defs.Helpers.Decoder.ExternalInput

@[expose] public section

namespace Tests.NonDeterminismDecoder
open Airbender Arithmetic Trace
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

def assignment : Nat → ZMod babyBearModulus
  | 2 | 19 | 27 => 4
  | 4 | 7 | 18 | 42 | 43 | 44 => 1
  | 21 => 8
  | 33 => 0x5678
  | 34 => 0x1234
  | _ => 0

def row : Row babyBearModulus := ⟨.addSub, assignment⟩
def regToken (index time value : Nat) : MemoryToken babyBearModulus :=
  ⟨(Cell.register (BitVec.ofNat 5 index)).addressCode, (time, 0), value⟩
def trace : Data babyBearModulus where
  rows := [row]
  rom := ROM.table [] []
  initial := row.start
  terminal := row.finish
  initialMemory := [regToken 0 0 0, regToken 1 0 0]
  terminalMemory := [regToken 0 5 0, regToken 1 6 (Nat.pair 0x5678 0x1234)]

theorem native_constraints : FlatOperation.ConstraintsHoldFlat
    (Verification.environment assignment) AddSub.clockConstraints := by
  simp [AddSub.clockConstraints, AddSub.importedConstraints,
    AddSub.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat,
    Expression.eval, Verification.environment, assignment]
  all_goals repeat' apply And.intro
  all_goals first
    | decide
    | (apply Verification.range16_contains
       norm_num [Expression.eval, Verification.environment, assignment, limbBase,
         ZMod.val_ofNat, ZMod.val_natCast, ZMod.val_one, babyBearModulus])
    | (apply Proofs.range_contains
       norm_num [Expression.eval, Verification.environment, assignment, timestampBase,
         ZMod.val_ofNat, ZMod.val_natCast, ZMod.val_one, babyBearModulus])

private theorem accepted : Accepted trace := by
  constructor
  · intro actual member
    have same := List.mem_singleton.mp member
    subst actual
    exact native_constraints
  · intro actual member
    have same := List.mem_singleton.mp member
    subst actual
    rfl
  · exact List.Perm.swap _ _ []
  · decide

private theorem clocks : ClockBoundary trace := by
  constructor
  · constructor <;> decide
  · decide
  · intro token member
    simp only [trace, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> constructor <;> decide

def later : Row babyBearModulus := ⟨.addSub, fun column =>
  if column = 2 then 8 else if column = 33 then 0x9999 else assignment column⟩
def hint : Row babyBearModulus := ⟨.addSub, fun column =>
  if column = 2 then 12 else if column = 18 then 0 else assignment column⟩
def reordered : Data babyBearModulus := { trace with rows := [row, hint, later] }

-- These three-row fixtures check consumption/order only, not native acceptance.
theorem clock_positions :
    NonDeterminism.readIndex reordered row = 0 ∧
    NonDeterminism.readIndex reordered later = 1 := by decide

theorem ordered_responses :
    NonDeterminism.consumed [hint, later, row] = [0x12345678, 0x12349999] := by decide

theorem chronological_ports :
    NonDeterminism.StreamPorts reordered [0x12345678, 0x12349999] := by
  intro actual member read
  simp only [reordered, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · decide
  · have absent : ¬ NonDeterminism.isRead hint = true := by decide
    exact False.elim (absent read)
  · decide

theorem swapped_stream_rejected :
    ¬ NonDeterminism.StreamPorts reordered [0x12349999, 0x12345678] := by
  intro ports
  have wrong := ports row (by simp [reordered]) (by decide)
  have unequal : (([0x12349999, 0x12345678] : List (BitVec 32))[NonDeterminism.readIndex reordered row]?) ≠ some (NonDeterminism.response row) := by decide
  exact unequal wrong

theorem short_stream_rejected :
    ¬ NonDeterminism.StreamPorts reordered [0x12345678] := by
  intro ports
  have missing := ports later (by simp [reordered]) (by decide)
  have absent : ([0x12345678] : List (BitVec 32))[NonDeterminism.readIndex reordered later]? = none := by decide
  change ([0x12345678] : List (BitVec 32))[NonDeterminism.readIndex reordered later]? = _ at missing
  rw [absent] at missing
  cases missing

end Tests.NonDeterminismDecoder
