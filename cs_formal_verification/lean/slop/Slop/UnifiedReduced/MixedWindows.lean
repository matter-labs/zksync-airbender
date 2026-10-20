import Human.Trace.UnifiedReduced.MixedWindows
import Slop.UnifiedReduced.MixedMemory
import Slop.UnifiedReduced.RequestWindows
import Slop.Delegation.NativeSegments

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384

theorem machine_port_offset (row : Trace.Row p UnifiedFamily) {port : MemoryPort}
    (member : port ∈ machinePorts row) : port.clock.offset < 3 := by
  have native := machine_port_native row member
  simp only [Trace.Row.ports, CircuitLayout.ports] at native
  simp [importedConstraintsMemoryPorts] at native
  rcases native with rfl | rfl | rfl
  all_goals decide

theorem instruction_window_clock {clock offset lower upper : Nat}
    (aligned : clock % 4 = 0) (first : lower % 4 = 0) (last : upper % 4 = 0)
    (small : offset < 4) (positive : 0 < lower) (ordered : lower ≤ upper) :
    (lower - 1 < clock + offset ∧ clock + offset ≤ upper - 1) ↔
      (lower ≤ clock ∧ clock < upper) := by omega

theorem worker_windows_shift [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {addresses : List (BitVec 32)}
    (accepted : RequestChecks data) (inputs : RequestInputs data before addresses)
    (requests : RequestBinding data before) {lower upper : Nat}
    (first : lower % 4 = 0) (last : upper % 4 = 0) (pastZero : 2 ≤ lower) :
    data.workers.windowRows lower upper = data.workers.windowRows (lower - 1) (upper - 1) := by
  apply List.filter_congr
  intro worker member
  have write := Delegation.Caller.Proofs.worker_write_time (by omega)
    (requests.clocks worker member).1 (requests.clocks worker member).2
  by_cases live : Delegation.Requests.Live (Delegation.Requests.fulfillment worker)
  · have bound := live_worker_clock hp inverse accepted inputs requests member live
    have time : worker.writeTime + 1 = workerClock worker := by
      rw [write]
      change ((decodeTimestamp worker.assignment worker.columns.invocation).value + 2) + 1 =
        (decodeTimestamp worker.assignment worker.columns.invocation).value + 3
      omega
    rw [← time] at bound
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    omega
  · have zero : (Delegation.Requests.fulfillment worker).time = (0, 0) := not_not.mp live
    have time : worker.writeTime = 2 := by simp [write, zero, timeOfPair, Timestamp.value]
    simp only [time]
    simp [Nat.not_lt.mpr pastZero, Nat.not_lt.mpr (by omega : 2 ≤ lower - 1)]

theorem mixed_window_steps [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {addresses : List (BitVec 32)}
    (accepted : RequestChecks data) (inputs : RequestInputs data before addresses)
    {lower upper : Nat} (first : lower % 4 = 0) (last : upper % 4 = 0) (pastZero : 2 ≤ lower) (ordered : lower ≤ upper) :
    data.windowSteps lower upper = Transfer.windowSteps (mixedData data) (lower - 1) (upper - 1) := by
  let selected := fun edge : MemoryToken p × MemoryToken p =>
    decide ((timeOfPair edge.2.time).value ≤ upper - 1) && !decide ((timeOfPair edge.2.time).value ≤ lower - 1)
  let steps := fun row : Trace.Row p UnifiedFamily => (machinePorts row).toList.map fun port =>
    (readToken row.assignment port, writeToken row.columns row.assignment port)
  have clocks := state_clock_inputs hp inverse accepted.constraints accepted.states
    inputs.initialClock inputs.initialAligned
  have rowFilter : ∀ row ∈ data.machine.rows, (steps row).filter selected =
      if decide (lower ≤ Delegation.Caller.startClock row ∧ Delegation.Caller.startClock row < upper)
      then steps row else [] := by
    intro row member
    have clock := clocks row member
    have aligned : Delegation.Caller.startClock row % 4 = 0 := by
      simpa [Delegation.Caller.startClock, Trace.Row.clock, Timestamp.value, timestampBase, Nat.add_mod, Nat.mul_mod]
        using clock.2
    have portFilter : ∀ edge ∈ steps row, selected edge =
        decide (lower ≤ Delegation.Caller.startClock row ∧ Delegation.Caller.startClock row < upper) := by
      intro edge present
      obtain ⟨port, included, rfl⟩ := List.mem_map.mp present
      have native := machine_port_native row (by simpa using included)
      have bounds := machine_port_offset row (by simpa using included)
      have time := (write_time (by omega) (base := rawPair row.assignment row.columns.initialTime)
        clock.1 clock.2 (by omega : port.clock.offset < 4)).2
      change (timeOfPair (writeToken row.columns row.assignment port).time).value =
        Delegation.Caller.startClock row + port.clock.offset at time
      simp only [selected, time]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq, Nat.not_le]
      exact and_comm.trans (instruction_window_clock aligned first last (by omega) (by omega) ordered)
    by_cases inside : lower ≤ Delegation.Caller.startClock row ∧ Delegation.Caller.startClock row < upper
    · simp only [decide_eq_true inside, ite_true]
      exact List.filter_eq_self.mpr (fun edge present => (portFilter edge present).trans (decide_eq_true inside))
    · simp only [decide_eq_false inside, Bool.false_eq_true, ite_false]
      apply List.filter_eq_nil_iff.mpr
      intro edge present
      rw [portFilter edge present, decide_eq_false inside]
      exact Bool.false_ne_true
  have machine : (data.windowMachineRows lower upper).flatMap steps =
      (data.machine.rows.flatMap steps).filter selected := by
    rw [List.filter_flatMap]
    calc
      _ = data.machine.rows.flatMap (fun row => if decide
          (lower ≤ Delegation.Caller.startClock row ∧ Delegation.Caller.startClock row < upper)
          then steps row else []) := filter_flatMap _ _ _
      _ = data.machine.rows.flatMap (fun row => (steps row).filter selected) :=
        List.flatMap_congr (fun row member => (rowFilter row member).symm)
  have requests := request_binding hp inverse accepted inputs
  have worker := Delegation.Proofs.native_window_steps data.workers (lower - 1) (upper - 1)
  change (data.workers.windowRows (lower - 1) (upper - 1)).flatMap Delegation.Row.memorySteps =
    Transfer.windowSteps (Delegation.Proofs.transferData data.workers) (lower - 1) (upper - 1) at worker
  rw [← worker_windows_shift hp inverse accepted inputs requests first last pastZero] at worker
  simpa only [RequestTrace.windowSteps, Transfer.windowSteps, Transfer.beforeSteps,
    Transfer.afterSteps, mixedData, RequestTrace.mixedSteps, Delegation.MemoryData.steps,
    Delegation.Proofs.transferData, Delegation.Proofs.windowRows,
    List.filter_append, List.filter_filter, steps, selected] using congrArg₂ (fun left right : List (MemoryToken p × MemoryToken p) => left ++ right) machine worker

theorem native_boundary {data : Transfer.Data p} {state : State} {cells : List Cell}
    (inputs : Transfer.NativeInputs data state cells) : NativeBoundary data.initial state cells :=
  ⟨Delegation.Proofs.transfer_boundary_image inputs,
    fun token member => ⟨inputs.words token member, inputs.clocks token member⟩⟩

theorem native_boundary_read {tokens : List (MemoryToken p)} {state : State} {cells : List Cell}
    (boundary : NativeBoundary tokens state cells) {token : MemoryToken p} (member : token ∈ tokens) :
    ∃ cell ∈ cells, cell.addressCode = token.address ∧ cell.read state = .ok token.word.toBitVec state := by
  obtain ⟨cell, present, value, address, read, word⟩ := boundary.1.values token member
  refine ⟨cell, present, address, ?_⟩
  rw [word, Word.ofBitVec_roundtrip]
  exact read

theorem mixed_window_execution [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    (rotationInverse : 64 * (-31457280 : ZMod p) = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program before ca oa cells)
    {lower upper : Nat} (first : lower % 4 = 0) (last : upper % 4 = 0) (pastZero : 2 ≤ lower) (ordered : lower ≤ upper) :
    MixedWindowExecution data before cells lower upper := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have requests := request_binding size clockInverse accepted.toRequestChecks inputs.publicProgram
  have facts := mixed_memory_facts size clockInverse accepted inputs.publicProgram inputs.initialization requests
  have initialized : Transfer.Inputs (mixedData data) before cells := ⟨inputs.initialization, inputs.distinct⟩
  have zeroRules := mixed_zero_rules size clockInverse accepted inputs requests
  have zeroReads := Transfer.read_cell_values_of_rules facts (Cell.register 0).addressCode 0
    (Delegation.Caller.Proofs.initial_zero inputs.initialization) zeroRules
  have zero : ∀ edge ∈ (mixedData data).steps, edge.1.address = (Cell.register 0).addressCode →
      memoryWord edge.2.value = 0 := by
    intro edge member same
    have value := zeroRules edge member same (fun previous present _ address => zeroReads previous present address)
    rw [value]
    rfl
  obtain ⟨start, finish, earlierEvents, spanEvents, atStart, atFinish, earlierFacts, selectedFacts,
      firstPerm, spanPerm, firstHistory, spanHistory, startInputs, finishInputs⟩ :=
    Transfer.split_native_sail_window facts initialized (mixed_write_rules hp rotationInverse accepted inputs)
      (mixed_write_clocks size clockInverse accepted inputs.publicProgram requests) inputs.aligned zero (lower - 1) (upper - 1)
  rw [← mixed_window_steps size clockInverse accepted.toRequestChecks inputs.publicProgram first last pastZero ordered]
    at selectedFacts spanPerm startInputs
  have prefixStepsEqual : Transfer.beforeSteps (mixedData data) (lower - 1) = data.prefixSteps lower := by
    apply List.filter_congr
    intro edge _
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    omega
  rw [prefixStepsEqual] at earlierFacts firstPerm
  exact ⟨request_windows size clockInverse accepted.toRequestChecks inputs.publicProgram first last pastZero,
    start, finish, earlierEvents, spanEvents, atStart, atFinish, firstPerm, spanPerm, firstHistory, spanHistory,
    earlierFacts.matching, selectedFacts.matching, native_boundary startInputs, native_boundary finishInputs⟩

theorem prefix_window_partition [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {ca : List (BitVec 32)}
    (accepted : RequestChecks data) (inputs : RequestInputs data before ca)
    {lower upper : Nat} (first : lower % 4 = 0) (last : upper % 4 = 0)
    (positive : 2 ≤ lower) (ordered : lower ≤ upper) :
    (data.prefixSteps lower ++ data.windowSteps lower upper).Perm (data.prefixSteps upper) := by
  rw [mixed_window_steps hp clockInverse accepted inputs first last positive ordered]
  have partition := List.filter_append_perm
    (fun edge : MemoryToken p × MemoryToken p => decide ((timeOfPair edge.2.time).value < lower))
    (data.prefixSteps upper)
  have earlier : (data.prefixSteps upper).filter (fun edge => decide
      ((timeOfPair edge.2.time).value < lower)) = data.prefixSteps lower := by
    rw [RequestTrace.prefixSteps, List.filter_filter]
    apply List.filter_congr
    intro edge _
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega
  have window : (data.prefixSteps upper).filter (fun edge => !decide
      ((timeOfPair edge.2.time).value < lower)) =
      Transfer.windowSteps (mixedData data) (lower - 1) (upper - 1) := by
    simp only [RequestTrace.prefixSteps, Transfer.windowSteps, Transfer.beforeSteps,
      Transfer.afterSteps, mixedData, List.filter_filter]
    apply List.filter_congr
    intro edge _
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
    omega
  rwa [earlier, window] at partition

theorem prefix_window_matching {initial start finish : List (MemoryToken p)}
    {earlier current : List (MemoryToken p × MemoryToken p)}
    (prefixMatching : (initial ++ earlier.map Prod.snd).Perm (start ++ earlier.map Prod.fst))
    (window : (start ++ current.map Prod.snd).Perm (finish ++ current.map Prod.fst)) :
    (initial ++ (earlier ++ current).map Prod.snd).Perm
      (finish ++ (earlier ++ current).map Prod.fst) := by
  apply List.perm_iff_count.mpr
  intro token
  have first := prefixMatching.count_eq token
  have last := window.count_eq token
  simp only [List.map_append, List.count_append] at first last ⊢
  omega

theorem native_suffix_split {raw : Transfer.Data p} {tokens : List (MemoryToken p)}
    {before : State} {cells : List Cell} {lower upper : Nat} (ordered : lower ≤ upper)
    (facts : Transfer.Facts ⟨tokens, raw.terminal, Transfer.afterSteps raw lower⟩)
    (inputs : Transfer.NativeInputs ⟨tokens, raw.terminal, Transfer.afterSteps raw lower⟩ before cells)
    (bounds : ∀ edge ∈ raw.steps, edge.2.word.Bounded)
    (clocks : ∀ edge ∈ raw.steps, (timeOfPair edge.2.time).Bounded)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (zero : ∀ edge ∈ raw.steps, edge.1.address = (Cell.register 0).addressCode → memoryWord edge.2.value = 0) :
    ∃ (finish : List (MemoryToken p)) (events : List MemoryAccess) (after : State),
      Transfer.Facts ⟨tokens, finish, Transfer.windowSteps raw lower upper⟩ ∧
      Transfer.Facts ⟨finish, raw.terminal, Transfer.afterSteps raw upper⟩ ∧
      events.Perm ((Transfer.windowSteps raw lower upper).map transferEvent) ∧
      SailHistory cells events before after ∧
      Transfer.NativeInputs ⟨finish, raw.terminal, Transfer.afterSteps raw upper⟩ after cells := by
  have rules : Transfer.WriteRules ⟨tokens, raw.terminal, Transfer.afterSteps raw lower⟩ := by
    intro edge member _
    exact bounds edge (List.mem_of_mem_filter member)
  obtain ⟨finish, events, after, earlier, later, permutation, _, actual, boundary⟩ :=
    Transfer.split_native_sail_state facts inputs rules
      (fun edge member => clocks edge (List.mem_of_mem_filter member)) aligned
      (fun edge member => zero edge (List.mem_of_mem_filter member)) upper
  have suffix : Transfer.afterSteps (⟨tokens, raw.terminal, Transfer.afterSteps raw lower⟩ : Transfer.Data p) upper =
      Transfer.afterSteps raw upper := by
    simp only [Transfer.afterSteps, List.filter_filter]
    apply List.filter_congr
    intro edge _
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
    omega
  rw [suffix] at later boundary
  exact ⟨finish, events, after, earlier, later, permutation, actual, boundary⟩

theorem mixed_prefix_steps [Fact p.Prime] (data : RequestTrace p) {cut : Nat} (positive : 0 < cut) :
    Transfer.beforeSteps (mixedData data) (cut - 1) = data.prefixSteps cut := by
  apply List.filter_congr
  intro edge _
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  omega

theorem matching_at_next_cut [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {ca : List (BitVec 32)}
    (accepted : RequestChecks data) (inputs : RequestInputs data before ca)
    {lower upper : Nat} {start finish : List (MemoryToken p)}
    (first : lower % 4 = 0) (last : upper % 4 = 0) (positive : 2 ≤ lower) (ordered : lower ≤ upper)
    (prefixMatching : (data.machine.initialMemory ++ (data.prefixSteps lower).map Prod.snd).Perm
      (start ++ (data.prefixSteps lower).map Prod.fst))
    (windowMatching : (start ++ (data.windowSteps lower upper).map Prod.snd).Perm
      (finish ++ (data.windowSteps lower upper).map Prod.fst)) :
    (data.machine.initialMemory ++ (data.prefixSteps upper).map Prod.snd).Perm
      (finish ++ (data.prefixSteps upper).map Prod.fst) := by
  have partition := prefix_window_partition hp clockInverse accepted inputs first last positive ordered
  have joined := prefix_window_matching prefixMatching windowMatching
  exact ((partition.map Prod.snd).symm.append_left _).trans
    (joined.trans ((partition.map Prod.fst).append_left _))

theorem mixed_window_chain [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1) (rotationInverse : 64 * (-31457280 : ZMod p) = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {a b c d : Nat}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program before ca oa cells)
    (aa : a % 4 = 0) (ba : b % 4 = 0) (ca' : c % 4 = 0) (da : d % 4 = 0)
    (positive : 2 ≤ a) (ab : a ≤ b) (bc : b ≤ c) (cd : c ≤ d) :
    MixedWindowChainExecution data before cells a b c d := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have requests := request_binding size clockInverse accepted.toRequestChecks inputs.publicProgram
  have facts := mixed_memory_facts size clockInverse accepted inputs.publicProgram inputs.initialization requests
  have initialized : Transfer.Inputs (mixedData data) before cells := ⟨inputs.initialization, inputs.distinct⟩
  have rules := mixed_write_rules hp rotationInverse accepted inputs
  have bounds : ∀ edge ∈ (mixedData data).steps, edge.2.word.Bounded := by
    intro edge member
    exact Transfer.produced_bounds facts initialized rules edge.2
      (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨edge, member, rfl⟩)))
  have clocks := mixed_write_clocks size clockInverse accepted inputs.publicProgram requests
  have zeroRules := mixed_zero_rules size clockInverse accepted inputs requests
  have zeroReads := Transfer.read_cell_values_of_rules facts (Cell.register 0).addressCode 0
    (Delegation.Caller.Proofs.initial_zero inputs.initialization) zeroRules
  have zero : ∀ edge ∈ (mixedData data).steps, edge.1.address = (Cell.register 0).addressCode → memoryWord edge.2.value = 0 := by
    intro edge member same
    have value := zeroRules edge member same (fun previous present _ address => zeroReads previous present address)
    rw [value]
    rfl
  obtain ⟨s1, ep, st1, prefixFacts, tail1, pp, _, hp1, n1⟩ :=
    Transfer.split_native_sail_state facts initialized.toNativeInputs rules clocks inputs.aligned zero (a - 1)
  obtain ⟨f1, e1, sf1, firstFacts, tail2, p1, h1, n2⟩ :=
    native_suffix_split (by omega : a - 1 ≤ b - 1) tail1 n1 bounds clocks inputs.aligned zero
  obtain ⟨s2, eg, st2, gapFacts, tail3, pg, hg, n3⟩ :=
    native_suffix_split (by omega : b - 1 ≤ c - 1) tail2 n2 bounds clocks inputs.aligned zero
  obtain ⟨f2, e2, sf2, secondFacts, _, p2, h2, n4⟩ :=
    native_suffix_split (by omega : c - 1 ≤ d - 1) tail3 n3 bounds clocks inputs.aligned zero
  rw [mixed_prefix_steps data (by omega)] at prefixFacts pp
  rw [← mixed_window_steps size clockInverse accepted.toRequestChecks inputs.publicProgram aa ba positive ab] at firstFacts p1
  rw [← mixed_window_steps size clockInverse accepted.toRequestChecks inputs.publicProgram ba ca' (by omega) bc] at gapFacts pg
  rw [← mixed_window_steps size clockInverse accepted.toRequestChecks inputs.publicProgram ca' da (by omega) cd] at secondFacts p2
  have prefixAtB := matching_at_next_cut size clockInverse accepted.toRequestChecks inputs.publicProgram
    aa ba positive ab prefixFacts.matching firstFacts.matching
  have prefixAtC := matching_at_next_cut size clockInverse accepted.toRequestChecks inputs.publicProgram
    ba ca' (by omega) bc prefixAtB gapFacts.matching
  let chain : WindowChain p := ⟨s1, f1, s2, f2, ep, e1, eg, e2, st1, sf1, st2, sf2⟩
  exact ⟨chain, ⟨pp, p1, pg, p2, hp1, h1, hg, h2, prefixFacts.matching, firstFacts.matching,
    prefixAtC, secondFacts.matching, native_boundary n1, native_boundary n2, native_boundary n3, native_boundary n4⟩⟩

theorem native_window_segments [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {before : State} {ca : List (BitVec 32)} {cells : List Cell}
    (accepted : RequestChecks data) (publicInputs : RequestInputs data before ca)
    (bounds : ∀ edge ∈ (mixedData data).steps, edge.2.word.Bounded)
    (clocks : ∀ edge ∈ (mixedData data).steps, (timeOfPair edge.2.time).Bounded)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (zero : ∀ edge ∈ (mixedData data).steps, edge.1.address = (Cell.register 0).addressCode → memoryWord edge.2.value = 0)
    {cut : Nat} {tokens : List (MemoryToken p)} {state : State} {windows : List (Nat × Nat)}
    (facts : Transfer.Facts ⟨tokens, (mixedData data).terminal, Transfer.afterSteps (mixedData data) (cut - 1)⟩)
    (inputs : Transfer.NativeInputs ⟨tokens, (mixedData data).terminal,
      Transfer.afterSteps (mixedData data) (cut - 1)⟩ state cells)
    (prefixMatching : (data.machine.initialMemory ++ (data.prefixSteps cut).map Prod.snd).Perm
      (tokens ++ (data.prefixSteps cut).map Prod.fst))
    (first : cut % 4 = 0) (positive : 2 ≤ cut) (ordered : WindowsOrdered cut windows) :
    ∃ segments, WindowSegmentsRealize data cells cut tokens state windows segments := by
  induction windows generalizing cut tokens state with
  | nil => exact ⟨[], trivial⟩
  | cons interval rest ih =>
    obtain ⟨lower, upper⟩ := interval
    obtain ⟨gapOrder, spanOrder, lowerAligned, upperAligned, restOrder⟩ := ordered
    obtain ⟨start, gapEvents, atStart, gapFacts, suffix, gapPerm, gapHistory, startInputs⟩ :=
      native_suffix_split (by omega : cut - 1 ≤ lower - 1) facts inputs bounds clocks aligned zero
    obtain ⟨finish, spanEvents, atFinish, spanFacts, remaining, spanPerm, spanHistory, finishInputs⟩ :=
      native_suffix_split (by omega : lower - 1 ≤ upper - 1) suffix startInputs bounds clocks aligned zero
    rw [← mixed_window_steps hp clockInverse accepted publicInputs first lowerAligned positive gapOrder] at gapFacts gapPerm
    rw [← mixed_window_steps hp clockInverse accepted publicInputs lowerAligned upperAligned (by omega) spanOrder]
      at spanFacts spanPerm
    have atLower := matching_at_next_cut hp clockInverse accepted publicInputs first lowerAligned positive gapOrder
      prefixMatching gapFacts.matching
    have atUpper := matching_at_next_cut hp clockInverse accepted publicInputs lowerAligned upperAligned (by omega) spanOrder
      atLower spanFacts.matching
    obtain ⟨segments, actual⟩ := ih remaining finishInputs atUpper upperAligned (by omega) restOrder
    let segment : WindowSegment p := ⟨start, finish, gapEvents, spanEvents, atStart, atFinish⟩
    exact ⟨segment :: segments, gapPerm, gapHistory, gapFacts.matching, atLower, spanPerm, spanHistory,
      spanFacts.matching, native_boundary startInputs, native_boundary finishInputs, actual⟩

theorem mixed_window_sequence [Fact p.Prime] (hp : 8388608 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1) (rotationInverse : 64 * (-31457280 : ZMod p) = 1)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {cut : Nat} {windows : List (Nat × Nat)}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program before ca oa cells)
    (first : cut % 4 = 0) (positive : 2 ≤ cut) (ordered : WindowsOrdered cut windows) :
    MixedWindowSequenceExecution data before cells cut windows := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have requests := request_binding size clockInverse accepted.toRequestChecks inputs.publicProgram
  have facts := mixed_memory_facts size clockInverse accepted inputs.publicProgram inputs.initialization requests
  have initialized : Transfer.Inputs (mixedData data) before cells := ⟨inputs.initialization, inputs.distinct⟩
  have rules := mixed_write_rules hp rotationInverse accepted inputs
  have bounds : ∀ edge ∈ (mixedData data).steps, edge.2.word.Bounded := by
    intro edge member
    exact Transfer.produced_bounds facts initialized rules edge.2
      (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨edge, member, rfl⟩)))
  have clocks := mixed_write_clocks size clockInverse accepted inputs.publicProgram requests
  have zeroRules := mixed_zero_rules size clockInverse accepted inputs requests
  have zeroReads := Transfer.read_cell_values_of_rules facts (Cell.register 0).addressCode 0
    (Delegation.Caller.Proofs.initial_zero inputs.initialization) zeroRules
  have zero : ∀ edge ∈ (mixedData data).steps, edge.1.address = (Cell.register 0).addressCode → memoryWord edge.2.value = 0 := by
    intro edge member same
    have value := zeroRules edge member same (fun previous present _ address => zeroReads previous present address)
    rw [value]
    rfl
  obtain ⟨tokens, events, state, prefixFacts, suffix, permutation, _, actual, boundary⟩ :=
    Transfer.split_native_sail_state facts initialized.toNativeInputs rules clocks inputs.aligned zero (cut - 1)
  rw [mixed_prefix_steps data (by omega)] at prefixFacts permutation
  obtain ⟨segments, realized⟩ := native_window_segments size clockInverse accepted.toRequestChecks inputs.publicProgram
    bounds clocks inputs.aligned zero suffix boundary prefixFacts.matching first positive ordered
  exact ⟨⟨tokens, events, state, segments⟩, permutation, actual, prefixFacts.matching, native_boundary boundary, realized⟩

end Airbender.UnifiedReduced.Caller.Proofs
