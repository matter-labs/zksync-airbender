module
public import Human.Trace.UnifiedReduced.RVCallerTheorems

@[expose] public section

/-! The two-window chain claims removed from `Human/Trace/UnifiedReduced/RVCallerTheorems.lean` (P4, D4) follow from
the kept sequence claims with the windows `[(a, b), (c, d)]` (an empty first gap). Their result definitions and
statements are kept here verbatim, and each is derived from its sequence claim. -/

namespace Airbender.UnifiedReduced.Caller
open Trace

/-- Retained tokens, events and actual states for two windows and their intervening gap. -/
structure RVWindowChain (p : Nat) where
  firstStart : List (MemoryToken p)
  firstFinish : List (MemoryToken p)
  secondStart : List (MemoryToken p)
  secondFinish : List (MemoryToken p)
  prefixEvents : List MemoryAccess
  firstEvents : List MemoryAccess
  gapEvents : List MemoryAccess
  secondEvents : List MemoryAccess
  atFirstStart : RV.State
  atFirstFinish : RV.State
  atSecondStart : RV.State
  atSecondFinish : RV.State

/-- Each segment executes from the preceding actual state. Matching and native
    boundary images retain every architectural port and the original raw clocks. -/
structure RVWindowChain.Realizes [Fact p.Prime] (chain : RVWindowChain p) (data : RVRequestTrace p)
    (before : RV.State) (cells : List Cell) (firstLower firstUpper secondLower secondUpper : Nat) : Prop where
  prefixPerm : chain.prefixEvents.Perm ((data.prefixSteps firstLower).map transferEvent)
  firstPerm : chain.firstEvents.Perm ((data.windowSteps firstLower firstUpper).map transferEvent)
  gapPerm : chain.gapEvents.Perm ((data.windowSteps firstUpper secondLower).map transferEvent)
  secondPerm : chain.secondEvents.Perm ((data.windowSteps secondLower secondUpper).map transferEvent)
  prefixHistory : RVHistory cells chain.prefixEvents before chain.atFirstStart
  firstHistory : RVHistory cells chain.firstEvents chain.atFirstStart chain.atFirstFinish
  gapHistory : RVHistory cells chain.gapEvents chain.atFirstFinish chain.atSecondStart
  secondHistory : RVHistory cells chain.secondEvents chain.atSecondStart chain.atSecondFinish
  firstPrefixMatching : (data.machine.initialMemory ++ (data.prefixSteps firstLower).map Prod.snd).Perm
    (chain.firstStart ++ (data.prefixSteps firstLower).map Prod.fst)
  firstMatching : (chain.firstStart ++ (data.windowSteps firstLower firstUpper).map Prod.snd).Perm
    (chain.firstFinish ++ (data.windowSteps firstLower firstUpper).map Prod.fst)
  secondPrefixMatching : (data.machine.initialMemory ++ (data.prefixSteps secondLower).map Prod.snd).Perm
    (chain.secondStart ++ (data.prefixSteps secondLower).map Prod.fst)
  secondMatching : (chain.secondStart ++ (data.windowSteps secondLower secondUpper).map Prod.snd).Perm
    (chain.secondFinish ++ (data.windowSteps secondLower secondUpper).map Prod.fst)
  firstStartBoundary : RVNativeBoundary chain.firstStart chain.atFirstStart cells
  firstFinishBoundary : RVNativeBoundary chain.firstFinish chain.atFirstFinish cells
  secondStartBoundary : RVNativeBoundary chain.secondStart chain.atSecondStart cells
  secondFinishBoundary : RVNativeBoundary chain.secondFinish chain.atSecondFinish cells

/-- A chain derived from one public initialization, with no supplied cut state. -/
def RVMixedWindowChainExecution [Fact p.Prime] (data : RVRequestTrace p) (before : RV.State)
    (cells : List Cell) (firstLower firstUpper secondLower secondUpper : Nat) : Prop :=
  ∃ chain : RVWindowChain p, chain.Realizes data before cells firstLower firstUpper secondLower secondUpper

/-- Two complete prepared references use the same continuous native history,
    including all intervening preparation and other worker effects. -/
structure RVPreparedHashChainResult [Fact p.Prime] (data : RVRequestTrace p) (before : RV.State)
    (cells : List Cell) (firstSpan secondSpan : Delegation.Caller.HashSpan)
    (firstLower firstUpper secondLower secondUpper : Nat) : Prop where
  firstRequests : Delegation.Caller.RequestWindowBinding data.callers data.workers firstLower firstUpper
  secondRequests : Delegation.Caller.RequestWindowBinding data.callers data.workers secondLower secondUpper
  firstCount : (Delegation.Caller.windowCallers data.callers firstLower firstUpper).length = firstSpan.callCount
  secondCount : (Delegation.Caller.windowCallers data.callers secondLower secondUpper).length = secondSpan.callCount
  execution : ∃ chain : RVWindowChain p,
    chain.Realizes data before cells firstLower firstUpper secondLower secondUpper ∧
    Delegation.Caller.HashSpan.RVResult firstSpan (data.windowProjection firstLower firstUpper chain.firstStart chain.firstFinish)
      chain.atFirstStart chain.atFirstFinish (Delegation.Caller.workerCells cells) ∧
    Delegation.Caller.HashSpan.RVResult secondSpan (data.windowProjection secondLower secondUpper chain.secondStart chain.secondFinish)
      chain.atSecondStart chain.atSecondFinish (Delegation.Caller.workerCells cells)

private theorem windowSteps_self [Fact p.Prime] (data : RVRequestTrace p) (cut : Nat) :
    data.windowSteps cut cut = [] := by
  have machine : data.windowMachineRows cut cut = [] :=
    List.filter_eq_nil_iff.mpr fun _ _ => by simp only [decide_eq_true_eq]; omega
  have workers : data.workers.windowRows cut cut = [] :=
    List.filter_eq_nil_iff.mpr fun _ _ => by simp only [decide_eq_true_eq]; omega
  simp only [RVRequestTrace.windowSteps, machine, workers, List.flatMap_nil, List.append_nil]

private theorem history_nil {cells : List Cell} {before after : RV.State} (history : RVHistory cells [] before after) :
    before = after := by
  cases history
  rfl

private theorem chain_of_sequence_realizes [Fact p.Prime] {sequence : RVWindowSequence p} {data : RVRequestTrace p}
    {before : RV.State} {cells : List Cell} {a b c d : Nat}
    (realized : sequence.Realizes data before cells a [(a, b), (c, d)]) :
    ∃ first second : RVWindowSegment p, sequence.segments = [first, second] ∧
      (⟨first.start, first.finish, second.start, second.finish, sequence.prefixEvents, first.spanEvents,
        second.gapEvents, second.spanEvents, first.atStart, first.atFinish, second.atStart, second.atFinish⟩ :
          RVWindowChain p).Realizes data before cells a b c d := by
  obtain ⟨prefixPerm, prefixHistory, _, _, segments⟩ := realized
  match h : sequence.segments, segments with
  | [first, second], segments =>
    obtain ⟨gapPerm, gapHistory, _, firstPrefix, firstPerm, firstHistory, firstMatching, firstStart, firstFinish,
      secondGapPerm, secondGapHistory, _, secondPrefix, secondPerm, secondHistory, secondMatching, secondStart,
      secondFinish, _⟩ := segments
    rw [windowSteps_self, List.map_nil, List.perm_nil] at gapPerm
    rw [gapPerm] at gapHistory
    rw [history_nil gapHistory] at prefixHistory
    exact ⟨first, second, rfl, ⟨prefixPerm, firstPerm, secondGapPerm, secondPerm, prefixHistory, firstHistory,
      secondGapHistory, secondHistory, firstPrefix, firstMatching, secondPrefix, secondMatching, firstStart,
      firstFinish, secondStart, secondFinish⟩⟩
  | [], segments => exact segments.elim
  | [_], segments => exact segments.2.2.2.2.2.2.2.2.2.elim
  | _ :: _ :: _ :: _, segments => exact segments.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.elim

end Airbender.UnifiedReduced.Caller

namespace Airbender.UnifiedReduced

-- The deleted `Caller.RVMixedWindowChainSoundnessClaim`, verbatim.
theorem Caller.Proofs.chain_of_sequence : Caller.RVMixedWindowSequenceSoundnessClaim → (
  ∀ {data : Caller.RVRequestTrace babyBearModulus} {program : List UnifiedReduced.RVProgramEntry} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {a b c d : Nat} (_accepted : Caller.RVMixedMemoryAccepted data program) (_inputs : Caller.RVMixedMemoryInputs data program before ca oa cells) (_aa : a % 4 = 0) (_ba : b % 4 = 0) (_ca' : c % 4 = 0) (_da : d % 4 = 0) (_positive : 2 ≤ a) (_ab : a ≤ b) (_bc : b ≤ c) (_cd : c ≤ d),
    Caller.RVMixedWindowChainExecution data before cells a b c d) := by
  intro sequence data program before ca oa cells a b c d accepted inputs aa ba ca' da positive ab bc cd
  obtain ⟨realization, realized⟩ := sequence (cut := a) (windows := [(a, b), (c, d)]) accepted inputs aa positive
    ⟨le_refl a, ab, aa, ba, bc, cd, ca', da, trivial⟩
  obtain ⟨_, _, _, chain⟩ := chain_of_sequence_realizes realized
  exact ⟨_, chain⟩

-- The deleted `Caller.RVPreparedHashChainSoundnessClaim`, verbatim.
theorem Caller.Proofs.prepared_hash_chain_of_sequence : Caller.RVPreparedHashSequenceSoundnessClaim → (
  ∀ {data : Caller.RVRequestTrace babyBearModulus} {before : RV.State} {ca oa : List (BitVec 32)} {cells : List Trace.Cell} {program : List UnifiedReduced.RVProgramEntry} {firstSpan secondSpan : Delegation.Caller.HashSpan} {a b c d : Nat} (_accepted : Caller.RVMixedMemoryAccepted data program) (_firstInputs : Caller.RVPreparedHashWindowInputs data before ca oa cells program firstSpan a b) (_secondInputs : Caller.RVPreparedHashWindowInputs data before ca oa cells program secondSpan c d) (_aa : a % 4 = 0) (_ba : b % 4 = 0) (_ca' : c % 4 = 0) (_da : d % 4 = 0) (_gap : b ≤ c),
    Caller.RVPreparedHashChainResult data before cells firstSpan secondSpan a b c d) := by
  intro sequence data before ca oa cells program firstSpan secondSpan a b c d accepted firstInputs secondInputs
    aa ba ca' da gap
  have ab := firstInputs.duration
  have cd := secondInputs.duration
  obtain ⟨realization, realized, results⟩ := sequence (first := ⟨firstSpan, a, b⟩) (rest := [⟨secondSpan, c, d⟩])
    accepted firstInputs
    (fun window member => by rw [List.mem_singleton] at member; subst member; exact secondInputs)
    ⟨le_refl a, by dsimp only; omega, aa, ba, gap, by dsimp only; omega, ca', da, trivial⟩
  obtain ⟨first, second, segments, chain⟩ := chain_of_sequence_realizes realized
  rw [segments] at results
  obtain ⟨⟨firstRequests, firstCount, firstResult⟩, ⟨secondRequests, secondCount, secondResult⟩, -⟩ :=
    List.forall₂_cons.mp results |>.imp id List.forall₂_cons.mp
  exact ⟨firstRequests, secondRequests, firstCount, secondCount, ⟨_, chain, firstResult, secondResult⟩⟩

end Airbender.UnifiedReduced
