import Airbender.Proofs.FullUnsigned.PrefixAcceptance

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail
open Delegation.Caller AddSub.Modular.External.Caller.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
variable [Fact babyBearModulus.Prime]

/-- A nonzero worker read in the caller's final slot comes from the actual
prefix frontier. Earlier CPU writes in that cycle touch x0. Other standard
and split workers use different aligned slots. No input value is assumed. -/
theorem unrolled_full_prefix_worker_read
    {initial : State} {text : List (BitVec 32)} {capacity : Nat}
    {masks : PooledFamily → NativeDecoder.ProgramRows.Mask}
    {columns : PooledFamily → List (List (ZMod babyBearModulus))}
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {splitWorkers : Keccak.Split.Native.MemoryData babyBearModulus}
    (setup : UnrolledProgramSetup .fullUnsigned initial text capacity masks columns)
    (lookup : UnrolledDecoderExactLookup trace masks columns)
    (accepted : UnrolledAcceptance trace workers splitWorkers.steps
      (splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)))
    (excluded : FullUnsigned.NoSpecial5Call initial text)
    (initialPC : trace.initial.word.lo < limbBase)
    (equations : Keccak.Split.Native.EquationsHold splitWorkers.cached splitWorkers.setup splitWorkers.rows)
    (active : ∀ row ∈ splitWorkers.rows, row.assignment (row.columns splitWorkers.cached).execute = 1)
    (initialClock : (timeOfPair trace.initial.timestamp).Bounded)
    (initialAligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    (facts : Transfer.Facts (unrolledFullMemoryData trace workers splitWorkers))
    (caller : Trace.Row babyBearModulus PooledFamily) (called : caller ∈ trace.rows)
    (family : caller.family = .addSub) (selected : Delegation.Requests.Selected caller.assignment)
    (positive : 0 < caller.clock)
    {memory : List (MemoryToken babyBearModulus)}
    (suffix : Transfer.Facts ⟨memory, trace.terminalMemory,
      Transfer.afterSteps (unrolledFullMemoryData trace workers splitWorkers) (caller.clock - 1)⟩)
    (edge : MemoryToken babyBearModulus × MemoryToken babyBearModulus)
    (member : edge ∈ (unrolledFullMemoryData trace workers splitWorkers).steps)
    (time : (timeOfPair edge.2.time).value = caller.clock + 3)
    (nonzero : edge.1.address ≠ (Cell.register 0).addressCode) : edge.1 ∈ memory := by
  have clocks := state_clock_inputs (by decide)
    (by decide +kernel : SerializedInverse.Clock babyBearModulus)
    accepted.cpuEquations accepted.states initialClock initialAligned
  have aligned (row : Trace.Row babyBearModulus PooledFamily) (present : row ∈ trace.rows) : row.clock % 4 = 0 := by
    simpa [Trace.Row.clock, decodeTimestamp, Timestamp.value, timestampBase, Nat.add_mod, Nat.mul_mod]
      using (clocks row present).2
  have cut := aligned caller called
  have order := facts.order edge member
  rw [time] at order
  have after : edge ∈ Transfer.afterSteps (unrolledFullMemoryData trace workers splitWorkers) (caller.clock - 1) := by
    apply List.mem_filter.mpr
    refine ⟨member, ?_⟩
    have late : ¬ (timeOfPair edge.2.time).value ≤ caller.clock - 1 := by rw [time]; omega
    simp [late]
  have source := suffix.matching.mem_iff.mpr
    (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨edge, after, rfl⟩)))
  rcases List.mem_append.mp source with seed | written
  · exact seed
  · obtain ⟨previous, late, equal⟩ := List.mem_map.mp written
    have original := (List.mem_filter.mp late).1
    have lateClock : caller.clock ≤ (timeOfPair previous.2.time).value := by
      by_contra tooEarly
      have early : (timeOfPair previous.2.time).value ≤ caller.clock - 1 := by omega
      have rejected := (List.mem_filter.mp late).2
      change (!decide ((timeOfPair previous.2.time).value ≤ caller.clock - 1)) = true at rejected
      rw [decide_eq_true early] at rejected
      cases rejected
    have beforeWorker : (timeOfPair previous.2.time).value < caller.clock + 3 := by
      rw [equal]
      exact order
    change previous ∈ pooledSteps trace ++ workers.steps ++ splitWorkers.steps at original
    rw [List.append_assoc] at original
    rcases List.mem_append.mp original with machine | rest
    · obtain ⟨other, included, physical⟩ := List.mem_flatMap.mp machine
      obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp physical
      dsimp only [Prod.fst, Prod.snd] at lateClock beforeWorker
      have event : transferEvent (readToken other.assignment port, writeToken other.columns other.assignment port) ∈
          machineEvents other := List.mem_map.mpr ⟨port, portMember, rfl⟩
      obtain ⟨offset, small, stamp⟩ := unrolled_cpu_event_time accepted initialClock initialAligned other included _ event
      change (timeOfPair (writeToken other.columns other.assignment port).time).value + 1 = other.clock + offset + 1 at stamp
      have otherAligned := aligned other included
      have sameClock : other.clock = caller.clock := by omega
      have unique := state_clocks_unique (by decide)
        (by decide +kernel : SerializedInverse.Clock babyBearModulus)
        accepted.cpuEquations accepted.states initialClock initialAligned
      change (trace.rows.map Trace.Row.clock).Nodup at unique
      have same := List.inj_on_of_nodup_map unique included called sameClock
      subst other
      have zero : (writeToken caller.columns caller.assignment port).address = (Cell.register 0).addressCode :=
        unrolled_full_caller_zero_ports setup lookup accepted excluded initialPC caller called family selected
          port (by simpa using portMember)
      have sameAddress := congrArg MemoryToken.address equal
      exact False.elim (nonzero (sameAddress.symm.trans zero))
    · rcases List.mem_append.mp rest with standard | split
      · obtain ⟨worker, included, physical⟩ := List.mem_flatMap.mp standard
        obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp physical
        dsimp only [Prod.fst, Prod.snd] at lateClock beforeWorker
        obtain ⟨other, present, _, _, _, slot⟩ := unrolled_full_standard_worker_slot
          accepted equations active initialClock initialAligned worker included
        have stamp := slot port (by simpa using portMember)
        change (timeOfPair (worker.writeToken port).time).value + 1 = other.clock + 4 at stamp
        have otherAligned := aligned other present
        omega
      · obtain ⟨worker, included, physical⟩ := List.mem_flatMap.mp split
        obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp physical
        dsimp only [Prod.fst, Prod.snd] at lateClock beforeWorker
        obtain ⟨other, present, _, _, _, slot⟩ := unrolled_full_split_worker_slot
          accepted equations active initialClock initialAligned worker included
        have stamp := slot port (by simpa using portMember)
        change (timeOfPair (worker.writeToken splitWorkers.cached port).time).value + 1 = other.clock + 4 at stamp
        have otherAligned := aligned other present
        omega

end Airbender.Compiler.MachineTargets.Proofs
