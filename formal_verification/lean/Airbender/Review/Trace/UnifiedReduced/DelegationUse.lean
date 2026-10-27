import Airbender.Review.Trace.UnifiedReduced.FullCalls
import Airbender.Review.Trace.Workers.Blake2G.Call
import Airbender.Review.Trace.Workers.Blake2Round.Call

namespace Airbender.UnifiedReduced.Caller
open Arithmetic Trace Reference.RiscV.Sail Reference.Sail

namespace DelegationUse

/-- Wrapper families in the current supported-use execution scope. The blessed
split Keccak wrapper is outside this scope (F12), rather than undefined behavior.
The legacy special5 circuit is not a blessed wrapper. -/
inductive Kind where
  | bigint
  | g (reduced : Bool)
  | round (reduced : Bool)
  deriving DecidableEq

def Kind.family : Kind → Delegation.Family
  | .bigint => .bigint
  | .g _ => .blakeG
  | .round _ => .blakeRound

def Kind.calls : Kind → Nat
  | .bigint => 1
  | .g reduced => Blake2G.callCount reduced
  | .round reduced => if reduced then 7 else 10

def Kind.preparation : Kind → Nat
  | .g _ => 1
  | _ => 0

/-- Public code interval, including the constant ADDI preceding a G bundle.
This descriptor contains no native row, assignment, clock or result. -/
structure Bundle where
  start : BitVec 32
  kind : Kind

def Bundle.instructions (bundle : Bundle) : Nat :=
  bundle.kind.preparation + bundle.kind.calls

def Bundle.instructionPC (bundle : Bundle) (index : Nat) : BitVec 32 :=
  bundle.start + BitVec.ofNat 32 (4 * index)

def Bundle.callPC (bundle : Bundle) (index : Nat) : BitVec 32 :=
  bundle.instructionPC (bundle.kind.preparation + index)

def csrInstruction (family : Delegation.Family) : SailRV32.instruction :=
  .CSRReg (BitVec.ofNat 12 (Delegation.Requests.csr family), .Regidx 0, .Regidx 0, .CSRRW)

/-- Public decoded program registries and the proposed partition into wrappers.
Image binding to actual bytes remains the execution theorem's existing public
input. Split Keccak and other unsupported instructions are not in this registry. -/
structure Program where
  ordinary : List UnifiedReduced.ProgramEntry
  callers : List Delegation.Caller.ProgramEntry
  bundles : List Bundle

/-- Exact instruction shapes, without treating the runtime mask or pointer
values as consequences of assembly syntax. Every registered delegation is
covered, and every slot of each wrapper is present in the public code registry. -/
structure Shapes (program : Program) : Prop where
  bounds : ∀ bundle ∈ program.bundles,
    bundle.start.toNat % 4 = 0 ∧
      bundle.start.toNat + 4 * bundle.instructions ≤ ROM.limit
  calls : ∀ bundle ∈ program.bundles, ∀ index : Fin bundle.kind.calls,
    ∃ entry ∈ program.callers, entry.pc = bundle.callPC index.val ∧
      entry.data.family = bundle.kind.family ∧ entry.instruction = csrInstruction bundle.kind.family
  preparation : ∀ bundle ∈ program.bundles, ∀ reduced, bundle.kind = .g reduced →
    ∃ entry ∈ program.ordinary, entry.pc = bundle.start ∧
      entry.instruction = .ITYPE (if reduced then 128 else 0, .Regidx 0, .Regidx 12, .ADDI)
  coverage : ∀ entry ∈ program.callers, ∃ bundle ∈ program.bundles,
    ∃ index : Fin bundle.kind.calls,
      entry.pc = bundle.callPC index.val ∧ entry.data.family = bundle.kind.family
  disjoint : ∀ one ∈ program.bundles, ∀ two ∈ program.bundles,
    ∀ i : Fin one.instructions, ∀ j : Fin two.instructions,
      one.instructionPC i.val = two.instructionPC j.val → one = two ∧ i.val = j.val

def ReadRegister (state : State) (index : BitVec 5) (value : BitVec 32) : Prop :=
  (Cell.register index).read state = .ok value state

def AtPC (state : State) (pc : BitVec 32) : Prop :=
  run (SailRV32.Functions.get_arch_pc ()) state = .ok pc state

/-- Runtime pointer obligations of the successful reference ABI. All addresses
are architectural words, without native address codes or worker port metadata. -/
def Pointers (kind : Kind) (left right : BitVec 32) : Prop :=
  ROM.limit ≤ left.toNat ∧ ROM.limit ≤ right.toNat ∧ left ≠ right ∧
    match kind with
    | .bigint => left.toNat % 32 = 0 ∧ right.toNat % 32 = 0
    | .g _ => left.toNat % 64 = 0 ∧ right.toNat % 64 = 0
    | .round _ => left.toNat % 128 = 0 ∧ right.toNat % 64 = 0

/-- The control value at an actual reference micro-call position. The round
mask uses the blessed callers' zero low limb. This is a property of reference
execution, not a supplied native control value or expected algorithm output. -/
def ControlAt (kind : Kind) (index : Nat) (value : BitVec 32) : Prop :=
  match kind with
  | .bigint => ∃ command : ExternalBoundary.BigintABI.Command, value = command.word.toBitVec
  | .g reduced => value = (Blake2G.controlAt reduced index).toBitVec
  | .round reduced => ∃ flags : Fin 8,
      (flags.val % 2 = 1 ↔ reduced = true) ∧ value = (Blake2Round.controlAt flags index).toBitVec

def ArgumentsAt (bundle : Bundle) (index : Nat) (state : State) : Prop :=
  ∃ left right control, ReadRegister state 10 left ∧ ReadRegister state 11 right ∧
    ReadRegister state 12 control ∧ Pointers bundle.kind left right ∧
      ControlAt bundle.kind index control

/-- Public, independent reference prefixes. The current registry admits
ordinary Sail/project instructions and the three covered delegation families.
All possible prefixes of that relation are quantified, without choosing a
successful final run or supplying a native witness history. -/
def Reachable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (program : Program) (initial state : State) : Prop :=
  Relation.ReflTransGen (FullStep program.ordinary program.callers) initial state

end DelegationUse

/-- Supported delegation use for the current modeled program registry. The
predicate depends only on public code and independent reference execution from
`initial`. Syntax, entry safety and runtime arguments are separate obligations.
It does not assert termination, native acceptance or an expected output.

The covered wrapper shapes are bigint, G and extended round. Blessed split
Keccak remains outside this registry (F12); special5 calls are excluded. This
predicate does not by itself assert native/reference prefix correspondence. -/
structure ValidDelegationUse [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (program : DelegationUse.Program) (initial : State) : Prop where
  shapes : DelegationUse.Shapes program
  /-- Starting execution inside a wrapper is prohibited, including G's first
  CSR instruction after its required constant ADDI. -/
  initialEntry : ∀ bundle ∈ program.bundles, ∀ index : Fin bundle.instructions,
    0 < index.val → ¬ DelegationUse.AtPC initial (bundle.instructionPC index.val)
  /-- Every reachable transition into a wrapper interior comes from its
  immediately preceding instruction. Indirect jumps and repeated invocations
  are included because the condition quantifies over reference prefixes. -/
  entry : ∀ before after, DelegationUse.Reachable program initial before →
    FullStep program.ordinary program.callers before after →
    ∀ bundle ∈ program.bundles, ∀ index : Fin bundle.instructions,
      0 < index.val → DelegationUse.AtPC after (bundle.instructionPC index.val) →
        DelegationUse.AtPC before (bundle.instructionPC (index.val - 1))
  /-- Valid masks, control schedule and pointers at every reachable call.
  No conclusion is inferred merely from the wrapper's syntactic shape. -/
  arguments : ∀ state, DelegationUse.Reachable program initial state →
    ∀ bundle ∈ program.bundles, ∀ index : Fin bundle.kind.calls,
      DelegationUse.AtPC state (bundle.callPC index.val) →
        DelegationUse.ArgumentsAt bundle index.val state

end Airbender.UnifiedReduced.Caller
