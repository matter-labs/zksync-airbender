import Airbender.Review.Helpers.UnifiedReduced.Windows

namespace Airbender.UnifiedReduced.Caller
open Trace Reference.RiscV.Sail

/-- Joint machine/worker memory transport between aligned instruction cuts. Both
    boundary states, reads and tokens come from one initialized history. This
    exposes control preparation effects; instruction retirement remains separate. -/
structure MixedWindowExecution [Fact p.Prime] (data : RequestTrace p) (before : State)
    (cells : List Cell) (lower upper : Nat) : Prop where
  /-- Exact selected caller/worker requests, counts and unique native slots. -/
  requests : Delegation.Caller.RequestWindowBinding data.callers data.workers lower upper
  /-- Complete selected rows, exact architectural matching and actual cut states. -/
  execution : ∃ (start finish : List (MemoryToken p)) (earlierEvents spanEvents : List MemoryAccess)
    (atStart atFinish : State),
    earlierEvents.Perm ((data.prefixSteps lower).map transferEvent) ∧
    spanEvents.Perm ((data.windowSteps lower upper).map transferEvent) ∧
    SailHistory cells earlierEvents before atStart ∧ SailHistory cells spanEvents atStart atFinish ∧
    (data.machine.initialMemory ++ (data.prefixSteps lower).map Prod.snd).Perm
      (start ++ (data.prefixSteps lower).map Prod.fst) ∧
    (start ++ (data.windowSteps lower upper).map Prod.snd).Perm
      (finish ++ (data.windowSteps lower upper).map Prod.fst) ∧
    NativeBoundary start atStart cells ∧ NativeBoundary finish atFinish cells

/-- Retained tokens, events and actual states for two windows and their intervening gap. -/
structure WindowChain (p : Nat) where
  firstStart : List (MemoryToken p)
  firstFinish : List (MemoryToken p)
  secondStart : List (MemoryToken p)
  secondFinish : List (MemoryToken p)
  prefixEvents : List MemoryAccess
  firstEvents : List MemoryAccess
  gapEvents : List MemoryAccess
  secondEvents : List MemoryAccess
  atFirstStart : State
  atFirstFinish : State
  atSecondStart : State
  atSecondFinish : State

/-- Each segment executes from the preceding actual state. Matching and native
    boundary images retain every architectural port and the original raw clocks. -/
structure WindowChain.Realizes [Fact p.Prime] (chain : WindowChain p) (data : RequestTrace p)
    (before : State) (cells : List Cell) (firstLower firstUpper secondLower secondUpper : Nat) : Prop where
  prefixPerm : chain.prefixEvents.Perm ((data.prefixSteps firstLower).map transferEvent)
  firstPerm : chain.firstEvents.Perm ((data.windowSteps firstLower firstUpper).map transferEvent)
  gapPerm : chain.gapEvents.Perm ((data.windowSteps firstUpper secondLower).map transferEvent)
  secondPerm : chain.secondEvents.Perm ((data.windowSteps secondLower secondUpper).map transferEvent)
  prefixHistory : SailHistory cells chain.prefixEvents before chain.atFirstStart
  firstHistory : SailHistory cells chain.firstEvents chain.atFirstStart chain.atFirstFinish
  gapHistory : SailHistory cells chain.gapEvents chain.atFirstFinish chain.atSecondStart
  secondHistory : SailHistory cells chain.secondEvents chain.atSecondStart chain.atSecondFinish
  firstPrefixMatching : (data.machine.initialMemory ++ (data.prefixSteps firstLower).map Prod.snd).Perm
    (chain.firstStart ++ (data.prefixSteps firstLower).map Prod.fst)
  firstMatching : (chain.firstStart ++ (data.windowSteps firstLower firstUpper).map Prod.snd).Perm
    (chain.firstFinish ++ (data.windowSteps firstLower firstUpper).map Prod.fst)
  secondPrefixMatching : (data.machine.initialMemory ++ (data.prefixSteps secondLower).map Prod.snd).Perm
    (chain.secondStart ++ (data.prefixSteps secondLower).map Prod.fst)
  secondMatching : (chain.secondStart ++ (data.windowSteps secondLower secondUpper).map Prod.snd).Perm
    (chain.secondFinish ++ (data.windowSteps secondLower secondUpper).map Prod.fst)
  firstStartBoundary : NativeBoundary chain.firstStart chain.atFirstStart cells
  firstFinishBoundary : NativeBoundary chain.firstFinish chain.atFirstFinish cells
  secondStartBoundary : NativeBoundary chain.secondStart chain.atSecondStart cells
  secondFinishBoundary : NativeBoundary chain.secondFinish chain.atSecondFinish cells

/-- A chain derived from one public initialization, with no supplied cut state. -/
def MixedWindowChainExecution [Fact p.Prime] (data : RequestTrace p) (before : State)
    (cells : List Cell) (firstLower firstUpper secondLower secondUpper : Nat) : Prop :=
  ∃ chain : WindowChain p, chain.Realizes data before cells firstLower firstUpper secondLower secondUpper

/-- Public ordered, aligned window intervals; gaps and empty intervals are allowed. -/
def WindowsOrdered (cut : Nat) : List (Nat × Nat) → Prop
  | [] => True
  | (lower, upper) :: rest => cut ≤ lower ∧ lower ≤ upper ∧ lower % 4 = 0 ∧ upper % 4 = 0 ∧
      WindowsOrdered upper rest

/-- One window's actual states, native boundaries and preceding gap events. -/
structure WindowSegment (p : Nat) where
  start : List (MemoryToken p)
  finish : List (MemoryToken p)
  gapEvents : List MemoryAccess
  spanEvents : List MemoryAccess
  atStart : State
  atFinish : State

/-- Each gap starts at the previous window's actual finish. All ports, boundary
    values and raw timestamps remain in the same architectural memory execution. -/
def WindowSegmentsRealize [Fact p.Prime] (data : RequestTrace p) (cells : List Cell) :
    Nat → List (MemoryToken p) → State → List (Nat × Nat) → List (WindowSegment p) → Prop
  | _, _, _, [], [] => True
  | cut, tokens, state, (lower, upper) :: rest, segment :: segments =>
      segment.gapEvents.Perm ((data.windowSteps cut lower).map transferEvent) ∧
      SailHistory cells segment.gapEvents state segment.atStart ∧
      (tokens ++ (data.windowSteps cut lower).map Prod.snd).Perm
        (segment.start ++ (data.windowSteps cut lower).map Prod.fst) ∧
      (data.machine.initialMemory ++ (data.prefixSteps lower).map Prod.snd).Perm
        (segment.start ++ (data.prefixSteps lower).map Prod.fst) ∧
      segment.spanEvents.Perm ((data.windowSteps lower upper).map transferEvent) ∧
      SailHistory cells segment.spanEvents segment.atStart segment.atFinish ∧
      (segment.start ++ (data.windowSteps lower upper).map Prod.snd).Perm
        (segment.finish ++ (data.windowSteps lower upper).map Prod.fst) ∧
      NativeBoundary segment.start segment.atStart cells ∧
      NativeBoundary segment.finish segment.atFinish cells ∧
      WindowSegmentsRealize data cells upper segment.finish segment.atFinish rest segments
  | _, _, _, _, _ => False

/-- A retained initial cut followed by a list of continuous native windows. -/
structure WindowSequence (p : Nat) where
  initial : List (MemoryToken p)
  prefixEvents : List MemoryAccess
  atInitial : State
  segments : List (WindowSegment p)

/-- Public initialization supplies the prefix; every subsequent state is linked
    by actual memory execution. Instruction retirement remains separate. -/
structure WindowSequence.Realizes [Fact p.Prime] (sequence : WindowSequence p) (data : RequestTrace p)
    (before : State) (cells : List Cell) (cut : Nat) (windows : List (Nat × Nat)) : Prop where
  prefixPerm : sequence.prefixEvents.Perm ((data.prefixSteps cut).map transferEvent)
  prefixHistory : SailHistory cells sequence.prefixEvents before sequence.atInitial
  prefixMatching : (data.machine.initialMemory ++ (data.prefixSteps cut).map Prod.snd).Perm
    (sequence.initial ++ (data.prefixSteps cut).map Prod.fst)
  boundary : NativeBoundary sequence.initial sequence.atInitial cells
  segments : WindowSegmentsRealize data cells cut sequence.initial sequence.atInitial windows sequence.segments

/-- An arbitrary finite window sequence with no supplied intermediate state. -/
def MixedWindowSequenceExecution [Fact p.Prime] (data : RequestTrace p) (before : State)
    (cells : List Cell) (cut : Nat) (windows : List (Nat × Nat)) : Prop :=
  ∃ sequence : WindowSequence p, sequence.Realizes data before cells cut windows

end Airbender.UnifiedReduced.Caller
