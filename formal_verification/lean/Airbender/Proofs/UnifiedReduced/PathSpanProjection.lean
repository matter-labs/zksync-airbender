import Airbender.Review.Trace.UnifiedReduced.Paths.SpanProjection
import Airbender.Proofs.UnifiedReduced.PathSpans
import Airbender.Proofs.Trace.InterleavedProjection
import Airbender.Proofs.Delegation.IntervalFold
import Airbender.Proofs.Trace.CycleComposition

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Trace.Proofs Arithmetic Reference.RiscV.Sail Reference.Sail
set_option warningAsError true

/-- RAM-readonly forms are original ordinary instructions, hence cannot
    secretly issue a delegation worker. -/
theorem path_ram_readonly_not_caller {instruction : SailRV32.instruction}
    (form : PathRamReadOnlyInstruction instruction) : Delegation.Caller.decoderFields instruction = none := by
  cases form with
  | write form =>
    cases form with
    | arithmetic form => cases form <;> rfl
    | binary form => cases form <;> rfl
    | comparison form => cases form <;> rfl
    | custom form => cases form <;> rfl
  | load => rfl
  | branch => rfl
  | jal => rfl
  | jalr => rfl

/-- Original public syntax derives the native GPR destination bank. Discarded
    arithmetic writes retain their native NOP projection; no store is admitted. -/
theorem path_ram_readonly_fields {instruction : SailRV32.instruction}
    {fields : DecoderData UnifiedFamily} (form : PathRamReadOnlyInstruction instruction)
    (decoded : Mixed.decoderFields instruction = some fields) :
    fields.mask < 524288 ∧ fields.mask.testBit 18 = false := by
  cases form with
  | @write instruction destination form =>
    by_cases zero : destination = 0#5
    · subst destination
      cases form with
      | arithmetic form =>
        cases form <;> simp [Mixed.decoderFields, UnifiedReduced.decoderFields, Trace.decoderFields,
          UnifiedReduced.arithmeticFields, Trace.arithmeticFields, DecoderData.mapFamily] at decoded
        all_goals subst fields
        all_goals decide
      | binary form =>
        cases form <;> simp [Mixed.decoderFields, UnifiedReduced.decoderFields, Trace.decoderFields,
          JumpBranchSlt.decoderFields, ShiftBinop.decoderFields, ShiftBinop.instructionFields,
          customDecoderFields] at decoded
      | comparison form =>
        cases form <;> simp [Mixed.decoderFields, UnifiedReduced.decoderFields, Trace.decoderFields,
          JumpBranchSlt.decoderFields, ShiftBinop.decoderFields, customDecoderFields] at decoded
      | custom form =>
        cases form <;> simp [Mixed.decoderFields, UnifiedReduced.decoderFields, Trace.decoderFields,
          JumpBranchSlt.decoderFields, ShiftBinop.decoderFields, customDecoderFields] at decoded
    · have result := public_register_write_fields form zero decoded
      exact ⟨result.2.1, result.2.2⟩
  | load immediate source destination =>
    by_cases zero : destination = 0#5
    · simp [Mixed.decoderFields, UnifiedReduced.decoderFields, Trace.decoderFields,
        Trace.arithmeticFields, UnifiedReduced.arithmeticFields, DecoderData.mapFamily, zero] at decoded
      subst fields
      exact ⟨by change 1 < 524288; decide, by change (1 : Nat).testBit 18 = false; decide⟩
    · simp [Mixed.decoderFields, UnifiedReduced.decoderFields, Trace.decoderFields,
        UnifiedReduced.arithmeticFields, DecoderData.mapFamily, zero] at decoded
      subst fields
      exact ⟨by change 131072 < 524288; decide, by change (131072 : Nat).testBit 18 = false; decide⟩
  | branch immediate right left operation =>
    simp [Mixed.decoderFields, UnifiedReduced.decoderFields, Trace.decoderFields,
      JumpBranchSlt.decoderFields, jumpFields, DecoderData.mapFamily] at decoded
    subst fields
    exact ⟨by change 24576 < 524288; decide, by change (24576 : Nat).testBit 18 = false; decide⟩
  | jal immediate destination =>
    by_cases zero : destination = 0#5
    · simp [Mixed.decoderFields, UnifiedReduced.decoderFields, Trace.decoderFields,
        JumpBranchSlt.decoderFields, jumpFields, DecoderData.mapFamily, zero] at decoded
      subst fields
      exact ⟨by change 17408 < 524288; decide, by change (17408 : Nat).testBit 18 = false; decide⟩
    · simp [Mixed.decoderFields, UnifiedReduced.decoderFields, Trace.decoderFields,
        JumpBranchSlt.decoderFields, jumpFields, DecoderData.mapFamily, zero] at decoded
      subst fields
      exact ⟨by change 1024 < 524288; decide, by change (1024 : Nat).testBit 18 = false; decide⟩
  | jalr immediate source destination =>
    by_cases zero : destination = 0#5
    · simp [Mixed.decoderFields, UnifiedReduced.decoderFields, Trace.decoderFields,
        JumpBranchSlt.decoderFields, jumpFields, DecoderData.mapFamily, zero] at decoded
      subst fields
      exact ⟨by change 18432 < 524288; decide, by change (18432 : Nat).testBit 18 = false; decide⟩
    · simp [Mixed.decoderFields, UnifiedReduced.decoderFields, Trace.decoderFields,
        JumpBranchSlt.decoderFields, jumpFields, DecoderData.mapFamily, zero] at decoded
      subst fields
      exact ⟨by change 2048 < 524288; decide, by change (2048 : Nat).testBit 18 = false; decide⟩

/-- A readonly ordinary row's destination is a GPR. Native RAM read ports
    retain their values, including LW timestamps; all other native effects stay. -/
theorem path_ram_readonly_row_refreshes [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {initial : State}
    {oa : List (BitVec 32)} {cut : Nat} {instruction : SailRV32.instruction}
    (accepted : MixedMemoryAccepted data program)
    (ordinaryProgram : Mixed.programImage initial oa = some program)
    (scope : PathInstructionPreparation data program cut instruction)
    (form : PathRamReadOnlyInstruction instruction)
    {w : Nat → ZMod p} (member : (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∈ data.machine.rows)
    (ordinary : (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) ∉ data.callers)
    (last : Delegation.Caller.startClock (⟨.machine, w⟩ : Trace.Row p UnifiedFamily) + 4 = cut)
    {port : MemoryPort} (portMember : port ∈ machinePorts (⟨.machine, w⟩ : Trace.Row p UnifiedFamily))
    {address : BitVec 32} (ram : port.address.code w = (Cell.ram address).addressCode) :
    (writeToken importedConstraintsTraceColumns w port).value = (readToken w port).value := by
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints data.machine.rom) importedConstraintsTimestampLookups)
  obtain ⟨entry, present, query, _, encoding⟩ := path_instruction_entry (by norm_num [timestampBase]; omega)
    accepted ordinaryProgram scope member ordinary last
  have fields := (run_program_sources ordinaryProgram entry present).fields
  rw [encoding] at fields
  obtain ⟨bound, bank⟩ := path_ram_readonly_fields form fields
  have flags := UnifiedReduced.Proofs.decoder_selectors (by omega) core bound query
  have registerBank : w 29 = 0 := by
    simpa [importedConstraintsDecoderColumns, bank] using flags 18
  rw [machine_ports_ordinary member ordinary] at portMember
  simp [Trace.Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts] at portMember
  rcases portMember with rfl | rfl | rfl
  · rfl
  · rfl
  · simp [MemoryAddress.code, Cell.addressCode, pairCode, registerBank] at ram

/-- The entire actual ordinary occurrence is RAM readonly. Original decoding
    derives the absence of workers; no event or timestamp is removed. -/
theorem path_ram_readonly_refreshes [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {initial : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {cut : Nat} {instruction : SailRV32.instruction}
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data initial ca)
    (ordinaryProgram : Mixed.programImage initial oa = some program)
    (image : initialImage initial cells = some data.machine.initialMemory)
    (scope : PathInstructionPreparation data program cut instruction)
    (form : PathRamReadOnlyInstruction instruction) (aligned : cut % 4 = 0) :
    ∀ edge ∈ data.windowSteps (cut - 4) cut, ∀ address : BitVec 32,
      edge.1.address = (Cell.ram address).addressCode → edge.2.value = edge.1.value := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have empty := path_instruction_workers_empty hp inverse accepted publicProgram ordinaryProgram image
    scope (path_ram_readonly_not_caller form) aligned
  intro edge included address ram
  rcases List.mem_append.mp included with machine | worker
  · obtain ⟨row, selected, step⟩ := List.mem_flatMap.mp machine
    obtain ⟨member, range⟩ := List.mem_filter.mp selected
    have range := of_decide_eq_true range
    have clocks := machine_clock_facts size inverse accepted.toRequestChecks publicProgram member
    have last : Delegation.Caller.startClock row + 4 = cut := by omega
    have ordinary := path_instruction_ordinary size accepted publicProgram ordinaryProgram scope
      (path_ram_readonly_not_caller form) member last
    obtain ⟨port, present, rfl⟩ := List.mem_map.mp step
    cases row with
    | mk kind w =>
      cases kind
      exact path_ram_readonly_row_refreshes hp accepted ordinaryProgram scope form member ordinary last
        (by simpa using present) ram
  · obtain ⟨row, selected, _⟩ := List.mem_flatMap.mp worker
    rw [empty] at selected
    cases selected

/-- Strict occurrence order excludes another span call between adjacent
    indices, independently of the actual PCs visited there. -/
theorem path_span_gap_no_owned_cut [Fact p.Prime]
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    (span : PathCompleteSpan data program) {i j : Fin span.span.callCount}
    (adjacent : j.val = i.val + 1) {cut : Nat}
    (after : span.start i + 8 ≤ cut) (before : cut ≤ span.start j) :
    ¬ ∃ k : Fin span.span.callCount, cut = span.start k + 4 := by
  rintro ⟨k, equal⟩
  by_cases earlier : k ≤ i
  · have monotone := span.increasing.monotone earlier
    omega
  have lower : i < k := lt_of_not_ge earlier
  by_cases later : j ≤ k
  · have monotone := span.increasing.monotone later
    omega
  have upper : k < j := lt_of_not_ge later
  change i.val < k.val at lower
  change k.val < j.val at upper
  omega

/-- Public ordinary syntax excludes every worker in the actual adjacent-call
    gap. The empty gap pool is a conclusion of native request matching. -/
theorem path_span_gap_workers_empty [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {initial : State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : ProtocolContextInputs data initial ca oa cells program)
    (span : PathCompleteSpan data program) (gaps : PathSpanReadOnlyGaps span)
    {i j : Fin span.span.callCount} (adjacent : j.val = i.val + 1) :
    data.workers.windowRows (span.start i + 4) (span.start j) = [] := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have first := span.aligned i
  have last := span.aligned j
  have floor := path_controller_dataflow_after_initial (span.control i)
  have ascending := span.increasing (show i < j by change i.val < j.val; omega)
  have firstStart : span.start (PathCompleteSpan.first span.span) ≤ span.start i :=
    span.increasing.monotone (by change 0 ≤ i.val; omega)
  have lastStart : span.start j ≤ span.start (PathCompleteSpan.last span.span) :=
    span.increasing.monotone (by change j.val ≤ span.span.callCount - 1; have := j.isLt; omega)
  have requests := request_windows size inverse accepted.toRequestChecks inputs.publicProgram
    (by omega : (span.start i + 4) % 4 = 0) last (by omega : 2 ≤ span.start i + 4)
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro worker selected
  obtain ⟨caller, matched, _⟩ := requests.workerMatches worker selected
  have called := List.mem_of_mem_filter matched.1
  have member := List.mem_of_mem_filter called
  have range := of_decide_eq_true (List.mem_filter.mp matched.1).2
  have clocks := machine_clock_facts size inverse accepted.toRequestChecks inputs.publicProgram member
  have nativeAligned := clocks.1
  have after : span.start i + 8 ≤ Delegation.Caller.startClock caller + 4 := by omega
  have before : Delegation.Caller.startClock caller + 4 ≤ span.start j := by omega
  obtain ⟨instruction, scope, form, _⟩ := gaps.code (Delegation.Caller.startClock caller + 4)
    (by omega) (by omega) (by omega) (path_span_gap_no_owned_cut span adjacent after before)
  exact path_instruction_ordinary size accepted inputs.publicProgram inputs.ordinaryProgram scope
    (path_ram_readonly_not_caller form) member rfl called

/-- Every actual RAM event in an adjacent-call gap refreshes its own old
    value. Ordinary GPR/link effects and all read timestamps are retained. -/
theorem path_span_gap_ram_refreshes [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {initial : State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : ProtocolContextInputs data initial ca oa cells program)
    (span : PathCompleteSpan data program) (gaps : PathSpanReadOnlyGaps span)
    {i j : Fin span.span.callCount} (adjacent : j.val = i.val + 1) :
    ∀ edge ∈ data.windowSteps (span.start i + 4) (span.start j), ∀ address : BitVec 32,
      edge.1.address = (Cell.ram address).addressCode → edge.2.value = edge.1.value := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have first := span.aligned i
  have last := span.aligned j
  have empty := path_span_gap_workers_empty hp inverse accepted inputs span gaps adjacent
  have firstStart : span.start (PathCompleteSpan.first span.span) ≤ span.start i :=
    span.increasing.monotone (by change 0 ≤ i.val; omega)
  have lastStart : span.start j ≤ span.start (PathCompleteSpan.last span.span) :=
    span.increasing.monotone (by change j.val ≤ span.span.callCount - 1; have := j.isLt; omega)
  intro edge included address ram
  rcases List.mem_append.mp included with machine | worker
  · obtain ⟨row, selected, step⟩ := List.mem_flatMap.mp machine
    obtain ⟨member, range⟩ := List.mem_filter.mp selected
    have range := of_decide_eq_true range
    have clocks := machine_clock_facts size inverse accepted.toRequestChecks inputs.publicProgram member
    have nativeAligned := clocks.1
    have after : span.start i + 8 ≤ Delegation.Caller.startClock row + 4 := by omega
    have before : Delegation.Caller.startClock row + 4 ≤ span.start j := by omega
    obtain ⟨instruction, scope, form, _⟩ := gaps.code (Delegation.Caller.startClock row + 4)
      (by omega) (by omega) (by omega) (path_span_gap_no_owned_cut span adjacent after before)
    apply path_ram_readonly_refreshes hp inverse accepted inputs.publicProgram inputs.ordinaryProgram
      inputs.initialization scope form (by omega) edge _ address ram
    exact List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr
      ⟨row, List.mem_filter.mpr ⟨member, decide_eq_true (by omega)⟩, step⟩))
  · obtain ⟨worker, selected, _⟩ := List.mem_flatMap.mp worker
    rw [empty] at selected
    cases selected

/-- A protected RAM read survives the real gap history. LW/read refreshes
    stay present, and the native syntax-derived rule supplies the value frame. -/
theorem path_span_gap_ram_frame [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {initial before after : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {events : List MemoryAccess}
    (accepted : MixedMemoryAccepted data program) (inputs : ProtocolContextInputs data initial ca oa cells program)
    (span : PathCompleteSpan data program) (gaps : PathSpanReadOnlyGaps span)
    {i j : Fin span.span.callCount} (adjacent : j.val = i.val + 1)
    (history : SailHistory cells events before after)
    (permutation : events.Perm ((data.windowSteps (span.start i + 4) (span.start j)).map transferEvent))
    (address : BitVec 32) (aligned : address.toNat % 4 = 0) {value : BitVec 32}
    (read : (Cell.ram address).read before = .ok value before) :
    (Cell.ram address).read after = .ok value after := by
  apply history_cell_frame_of_refresh history inputs.aligned (Cell.ram address) aligned _ read
  intro event included same
  obtain ⟨edge, member, rfl⟩ := List.mem_map.mp (permutation.mem_iff.mp included)
  have raw := path_span_gap_ram_refreshes hp inverse accepted inputs span gaps adjacent edge member address same
  change memoryWord edge.2.value = memoryWord edge.1.value
  rw [raw]

/-- Actual cut states for every indexed call and every adjacent gap come
    from one global history. Determinism identifies overlapping cut witnesses. -/
theorem path_span_cut_states [Fact p.Prime]
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    {cells : List Cell} {events : List MemoryAccess} {initial finalState : State}
    (span : PathCompleteSpan data program)
    (order : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events initial finalState) :
    ∃ before after : Fin span.span.callCount → State,
      (∀ i, SailHistory cells (events.filter fun event => decide (event.1 ≤ span.start i)) initial (before i) ∧
        SailHistory cells (events.filter fun event => decide
          (span.start i < event.1 ∧ event.1 ≤ span.start i + 4)) (before i) (after i)) ∧
      ∀ i j, j.val = i.val + 1 →
        SailHistory cells (events.filter fun event => decide
          (span.start i + 4 < event.1 ∧ event.1 ≤ span.start j)) (after i) (before j) := by
  have each : ∀ i : Fin span.span.callCount, ∃ before after : State,
      SailHistory cells (events.filter fun event => decide (event.1 ≤ span.start i)) initial before ∧
      SailHistory cells (events.filter fun event => decide
        (span.start i < event.1 ∧ event.1 ≤ span.start i + 4)) before after := by
    intro i
    obtain ⟨before, after, _, past, current, _⟩ := history_window order history (by omega : span.start i ≤ span.start i + 4)
    exact ⟨before, after, past, current⟩
  choose before after histories using each
  refine ⟨before, after, histories, ?_⟩
  intro i j adjacent
  have first := span.aligned i
  have last := span.aligned j
  have ascending := span.increasing (show i < j by change i.val < j.val; omega)
  have bounds : span.start i + 4 ≤ span.start j := by omega
  obtain ⟨one, two, _, past, current, _⟩ := history_window order history bounds
  have firstPrefix := history_prefix_of_window order (by omega : span.start i ≤ span.start i + 4)
    (histories i).1 (histories i).2
  have oneEqual := sail_history_deterministic past firstPrefix
  have secondPrefix := history_prefix_of_window order bounds past current
  have twoEqual := sail_history_deterministic secondPrefix (histories j).1
  simpa only [oneEqual, twoEqual] using current

/-- Abstract finite composition of local view transitions and the separately
    proved real-gap view equations. This algebra changes no program semantics. -/
theorem path_interleaved_view_fold {α : Type*} {count : Nat} (positive : 0 < count)
    (before after : Fin count → α) (step : Nat → α → α)
    (calls : ∀ i, after i = step i.val (before i))
    (gaps : ∀ i j, j.val = i.val + 1 → before j = after i) :
    after ⟨count - 1, by omega⟩ =
      Fin.foldl count (fun value i => step i.val value) (before ⟨0, positive⟩) := by
  let states : Nat → α := fun i => if bound : i < count then before ⟨i, bound⟩ else after ⟨count - 1, by omega⟩
  have transitions : ∀ i < count, states (i + 1) = step i (states i) := by
    intro i bound
    by_cases next : i + 1 < count
    · have bridge := gaps ⟨i, bound⟩ ⟨i + 1, next⟩ rfl
      have call := calls ⟨i, bound⟩
      simpa only [states, dif_pos bound, dif_pos next] using bridge.trans call
    · have last : (⟨i, bound⟩ : Fin count) = ⟨count - 1, by omega⟩ :=
        Fin.ext (by change i = count - 1; omega)
      have call := calls ⟨i, bound⟩
      simpa only [states, dif_pos bound, dif_neg next, last] using call
  have result := Delegation.Proofs.interval_fold states step 0 count (by
    intro i bound
    simpa only [Nat.zero_add] using transitions i bound)
  simpa only [states, Nat.zero_add, dif_neg (Nat.lt_irrefl count), dif_pos positive] using result

/-- A reversed physical-state chain for the existing pure Keccak assembly
    interface, derived from forward call transitions and real gap equations. -/
theorem path_interleaved_reverse_chain {α : Type*} {count : Nat} (positive : 0 < count)
    (before after : Fin count → α) (step : Nat → α → α)
    (calls : ∀ i, after i = step i.val (before i))
    (gaps : ∀ i j, j.val = i.val + 1 → before j = after i) :
    ∃ states : Fin (count + 1) → α,
      states ⟨0, by omega⟩ = after ⟨count - 1, by omega⟩ ∧
      states ⟨count, by omega⟩ = before ⟨0, positive⟩ ∧
      ∀ i : Fin count, states ⟨i.val, by omega⟩ =
        step (count - 1 - i.val) (states ⟨i.val + 1, by omega⟩) := by
  let forward : Nat → α := fun i => if bound : i < count then before ⟨i, bound⟩ else after ⟨count - 1, by omega⟩
  have transitions : ∀ i < count, forward (i + 1) = step i (forward i) := by
    intro i bound
    by_cases next : i + 1 < count
    · have bridge := gaps ⟨i, bound⟩ ⟨i + 1, next⟩ rfl
      simpa only [forward, dif_pos bound, dif_pos next] using bridge.trans (calls ⟨i, bound⟩)
    · have last : (⟨i, bound⟩ : Fin count) = ⟨count - 1, by omega⟩ :=
        Fin.ext (by change i = count - 1; omega)
      simpa only [forward, dif_pos bound, dif_neg next, last] using calls ⟨i, bound⟩
  refine ⟨fun i => forward (count - i.val), ?_, ?_, ?_⟩
  · simp only [Nat.sub_zero, forward, dif_neg (Nat.lt_irrefl count)]
  · simp only [Nat.sub_self, forward, dif_pos positive]
  · intro i
    have bound := i.isLt
    have index : count - 1 - i.val < count := by omega
    have first : count - i.val = (count - 1 - i.val) + 1 := by omega
    have second : count - (i.val + 1) = count - 1 - i.val := by omega
    simpa only [first, second] using transitions (count - 1 - i.val) index

/-- Span pointer registers are nonzero and are read-refresh ports rather
    than the family's control-register write. -/
theorem path_span_pointer_register_properties (span : Delegation.Caller.HashSpan) {register : BitVec 5}
    (member : register ∈ path_span_pointer_registers span) :
    register ≠ 0 ∧ register ≠ callerControlRegister span.family := by
  cases span with
  | blakeG reduced =>
    simp only [path_span_pointer_registers, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · change (10 : BitVec 5) ≠ 0 ∧ (10 : BitVec 5) ≠ 12
      decide
    · change (11 : BitVec 5) ≠ 0 ∧ (11 : BitVec 5) ≠ 12
      decide
  | blakeRound flags =>
    simp only [path_span_pointer_registers, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · change (10 : BitVec 5) ≠ 0 ∧ (10 : BitVec 5) ≠ 12
      decide
    · change (11 : BitVec 5) ≠ 0 ∧ (11 : BitVec 5) ≠ 12
      decide
  | keccak =>
    simp only [path_span_pointer_registers, List.mem_singleton] at member
    subst register
    decide

/-- Public ordinary gaps plus the span's real caller occurrences derive all
    pointer GPR frames from the first call's upper cut to any later call.
    This retains arbitrary seed pointers for G, extended BLAKE and Keccak. -/
theorem path_span_pointer_frames [Fact p.Prime]
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    (span : PathCompleteSpan data program) (gaps : PathSpanReadOnlyGaps span)
    (target : Fin span.span.callCount) (afterFirst : 0 < target.val)
    {register : BitVec 5} (member : register ∈ path_span_pointer_registers span.span) :
    PathRegisterGapFrames data program
      (span.start (PathCompleteSpan.first span.span) + 4) (span.start target) register := by
  have firstAligned := span.aligned (PathCompleteSpan.first span.span)
  have targetAligned := span.aligned target
  have before : PathCompleteSpan.first span.span < target := by
    change 0 < target.val
    exact afterFirst
  have ascending := span.increasing before
  have floor := path_controller_dataflow_after_initial (span.control (PathCompleteSpan.first span.span))
  have upper := (span.code target).beforeTerminal
  have targetLast : span.start target ≤ span.start (PathCompleteSpan.last span.span) := by
    apply span.increasing.monotone
    change target.val ≤ span.span.callCount - 1
    have := target.isLt
    omega
  refine ⟨by omega, targetAligned, by omega, by omega, by omega, ?_⟩
  intro cut afterLower beforeUpper aligned
  by_cases owned : ∃ i : Fin span.span.callCount, cut = span.start i + 4
  · obtain ⟨i, rfl⟩ := owned
    exact .caller (span.code i) (path_span_pointer_register_properties span.span member).2
  · obtain ⟨instruction, scope, _, pointers⟩ := gaps.code cut afterLower
      (beforeUpper.trans targetLast) aligned owned
    exact .ordinary scope (pointers register member)

def path_span_pointer_port (span : Delegation.Caller.HashSpan) (register : BitVec 5) : MemoryPort :=
  match span with
  | .blakeG _ => if register = 10 then Blake2G.importedConstraintsMemoryPorts[0] else Blake2G.importedConstraintsMemoryPorts[5]
  | .blakeRound _ => if register = 10 then Blake2Round.importedConstraintsMemoryPorts[0] else Blake2Round.importedConstraintsMemoryPorts[25]
  | .keccak => Keccak.importedConstraintsMemoryPorts[1]

/-- Fixed native descriptors bind every span pointer to its own readonly GPR
    port. Other worker writes remain part of the actual native history. -/
theorem path_span_pointer_port_properties (span : Delegation.Caller.HashSpan) {register : BitVec 5}
    (member : register ∈ path_span_pointer_registers span) (worker : Delegation.Row p)
    (family : worker.family = span.family) :
    path_span_pointer_port span register ∈ worker.ports ∧
      (path_span_pointer_port span register).address.code worker.assignment = (Cell.register register).addressCode ∧
      (worker.writeToken (path_span_pointer_port span register)).value =
        (readToken worker.assignment (path_span_pointer_port span register)).value := by
  cases span with
  | blakeG reduced =>
    simp only [path_span_pointer_registers, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    all_goals cases worker with
    | mk kind w =>
      change kind = .blakeG at family
      subst kind
      exact ⟨Array.getElem_mem (by
        first | (change 0 < 9; decide) | (change 5 < 9; decide)), rfl, rfl⟩
  | blakeRound flags =>
    simp only [path_span_pointer_registers, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    all_goals cases worker with
    | mk kind w =>
      change kind = .blakeRound at family
      subst kind
      exact ⟨Array.getElem_mem (by
        first | (change 0 < 43; decide) | (change 25 < 43; decide)), rfl, rfl⟩
  | keccak =>
    simp only [path_span_pointer_registers, List.mem_singleton] at member
    subst register
    cases worker with
    | mk kind w =>
      change kind = .keccak at family
      subst kind
      exact ⟨Array.getElem_mem (by change 1 < Keccak.importedConstraintsMemoryPorts.size; decide), rfl, rfl⟩

private theorem path_span_append_pointer_call [Fact p.Prime]
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    {lower target : Nat} {register : BitVec 5} {family : Delegation.Family}
    (frames : PathRegisterGapFrames data program lower target register)
    (scope : PathCallerPreparation data (target + 4) family)
    (different : register ≠ callerControlRegister family) :
    PathRegisterGapFrames data program lower (target + 4) register := by
  refine ⟨frames.lowerAligned, by have := frames.upperAligned; omega,
    by have := frames.ordered; omega, frames.afterInitial, scope.beforeTerminal, ?_⟩
  intro cut afterLower beforeUpper aligned
  by_cases earlier : cut ≤ target
  · exact frames.code cut afterLower earlier aligned
  · have equal : cut = target + 4 := by have := frames.upperAligned; omega
    subst cut
    exact .caller scope different

/-- Arbitrary first native pointer words are canonicalized from derived word
    bounds and retained at every actual indexed call. Public code frames, not
    a homogeneous pool or literal pointer assumptions, supply the transport. -/
theorem path_span_pointer_values
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry} {initial : State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program initial ca oa cells)
    (span : PathCompleteSpan data program) (gaps : PathSpanReadOnlyGaps span)
    (rows : Fin span.span.callCount → Delegation.Row babyBearModulus)
    (members : ∀ i, rows i ∈ data.workers.windowRows (span.start i) (span.start i + 4))
    {register : BitVec 5} (pointer : register ∈ path_span_pointer_registers span.span) :
    ∃ value : BitVec 32, ∀ i,
      (readToken (rows i).assignment (path_span_pointer_port span.span register)).word = Word.ofBitVec value := by
  let first := PathCompleteSpan.first span.span
  let port := path_span_pointer_port span.span register
  have families (i : Fin span.span.callCount) : (rows i).family = span.span.family := by
    obtain ⟨_, window⟩ := path_caller_window (by decide) (by decide) accepted inputs.publicProgram
      inputs.ordinaryProgram inputs.initialization (span.code i) (by have := span.aligned i; omega)
    exact window.family (rows i) (by simpa using members i)
  have properties (i : Fin span.span.callCount) :=
    path_span_pointer_port_properties span.span pointer (rows i) (families i)
  let word := (readToken (rows first).assignment port).word
  have effects := mixed_memory_effects accepted inputs
  have bounded : word.Bounded :=
    (effects.words _ (mixed_worker_member (List.mem_of_mem_filter (members first)) (properties first).1)).1
  have canonical : Word.ofBitVec word.toBitVec = word := by
    apply Word.eq_of_value (Word.ofBitVec_bound _) bounded
    rw [Word.ofBitVec_value, Word.toBitVec_toNat bounded]
  have unique : (data.machine.initialMemory.map MemoryToken.address).Nodup := by
    rw [image_addresses inputs.initialization]
    exact inputs.distinct
  refine ⟨word.toBitVec, ?_⟩
  intro target
  by_cases zero : target.val = 0
  · have same : target = first := Fin.ext zero
    subst target
    exact canonical.symm
  have positive : 0 < target.val := by omega
  have frames := path_span_pointer_frames span gaps target positive pointer
  have nonzero := (path_span_pointer_register_properties span.span pointer).1
  have different := (path_span_pointer_register_properties span.span pointer).2
  have extended := path_span_append_pointer_call frames (span.code target) different
  have targetRange := of_decide_eq_true (List.mem_filter.mp (members target)).2
  have lower := frames.ordered
  change span.start first + 4 ≤ span.start target at lower
  have native : rows target ∈ data.workers.windowRows (span.start first + 4) (span.start target + 4) :=
    List.mem_filter.mpr ⟨List.mem_of_mem_filter (members target), decide_eq_true (by omega)⟩
  have included : (readToken (rows target).assignment port, (rows target).writeToken port) ∈
      data.windowSteps (span.start first + 4) (span.start target + 4) :=
    List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
      ⟨rows target, native, List.mem_map.mpr ⟨port, by simpa using (properties target).1, rfl⟩⟩))
  have raw := path_gap_read_value (by decide) (by decide) accepted inputs.publicProgram inputs.ordinaryProgram
    inputs.initialization unique extended nonzero (value := (readToken (rows first).assignment port).value)
    (by
      intro tokens matching
      obtain ⟨present, _⟩ := path_caller_write_boundary (by decide) (by decide) accepted inputs.publicProgram
        inputs.ordinaryProgram inputs.initialization (span.code first) (by have := span.aligned first; omega)
        matching (by simpa using members first) (properties first).1
      exact ⟨(rows first).writeToken port, present, (properties first).2.1, (properties first).2.2⟩)
    included (properties target).2.1
  have same : (readToken (rows target).assignment port).word = word := by
    change (readToken (rows target).assignment port).value = (readToken (rows first).assignment port).value at raw
    exact congrArg (fun value : Nat => (⟨(Nat.unpair value).1, (Nat.unpair value).2⟩ : Word)) raw
  exact same.trans canonical.symm

/-- Project the actual global event multiset to one native instruction-boundary
    interval. Clean's event clock is the native write clock plus one. -/
theorem path_window_events_permutation [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p timestampBase)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {initial : State} {ca : List (BitVec 32)} {events : List MemoryAccess}
    (accepted : RequestChecks data) (publicProgram : RequestInputs data initial ca)
    {lower upper : Nat} (first : lower % 4 = 0) (last : upper % 4 = 0)
    (positive : 2 ≤ lower) (bounds : lower ≤ upper)
    (permutation : events.Perm (data.mixedSteps.map transferEvent)) :
    (events.filter fun event => decide (lower < event.1 ∧ event.1 ≤ upper)).Perm
      ((data.windowSteps lower upper).map transferEvent) := by
  have chosen := permutation.filter fun event => decide (lower < event.1 ∧ event.1 ≤ upper)
  have same : ((data.mixedSteps.map transferEvent).filter fun event =>
      decide (lower < event.1 ∧ event.1 ≤ upper)) = (data.windowSteps lower upper).map transferEvent := by
    rw [mixed_window_steps hp inverse accepted publicProgram first last positive bounds]
    simp only [Transfer.windowSteps, Transfer.beforeSteps, Transfer.afterSteps, mixedData,
      List.filter_filter, List.filter_map]
    apply congrArg (List.map transferEvent)
    apply List.filter_congr
    intro edge _
    change decide (lower < (timeOfPair edge.2.time).value + 1 ∧
      (timeOfPair edge.2.time).value + 1 ≤ upper) =
      (decide ((timeOfPair edge.2.time).value ≤ upper - 1) &&
        !decide ((timeOfPair edge.2.time).value ≤ lower - 1))
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
    omega
  rw [same] at chosen
  exact chosen

/-- Every indexed worker obtains its real local history from the actual caller
    cycle. Request uniqueness identifies the same worker as the indexed native
    occurrence; only architectural x0 refreshes are removed by the established
    zero-cell identity, with all gap events left in their own real intervals. -/
theorem path_span_local_histories
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry} {initial : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {events : List MemoryAccess}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program initial ca oa cells)
    (span : PathCompleteSpan data program) (rows : Fin span.span.callCount → Delegation.Row babyBearModulus)
    (members : ∀ i, rows i ∈ data.workers.windowRows (span.start i) (span.start i + 4))
    (permutation : events.Perm (data.mixedSteps.map transferEvent))
    (before after : Fin span.span.callCount → State)
    (current : ∀ i, SailHistory cells (events.filter fun event => decide
      (span.start i < event.1 ∧ event.1 ≤ span.start i + 4)) (before i) (after i)) :
    ∀ i, ∃ localEvents : List MemoryAccess,
      SailHistory cells localEvents (before i) (after i) ∧
      localEvents.Perm ((rows i).memorySteps.map transferEvent) := by
  have effects := mixed_memory_effects accepted inputs
  intro i
  obtain ⟨_, window⟩ := path_caller_window (by decide) (by decide) accepted inputs.publicProgram
    inputs.ordinaryProgram inputs.initialization (span.code i) (by have := span.aligned i; omega)
  obtain ⟨caller, matched, _⟩ := window.requests.workerMatches (rows i) (by simpa using members i)
  have called := List.mem_of_mem_filter matched.1
  have nativeMember := List.mem_of_mem_filter called
  have range := of_decide_eq_true (List.mem_filter.mp matched.1).2
  have clocks := machine_clock_facts (by decide) (by decide) accepted.toRequestChecks inputs.publicProgram nativeMember
  have nativeAligned := clocks.1
  have aligned := span.aligned i
  have start : Delegation.Caller.startClock caller = span.start i := by omega
  have floor := path_controller_dataflow_after_initial (span.control i)
  have positive : 0 < Delegation.Caller.startClock caller := by omega
  have cycle := cycle_window_permutation (by decide) (by decide) accepted.toRequestChecks
    inputs.publicProgram effects.requests permutation nativeMember positive
  have currentCall : SailHistory cells (events.filter fun event => decide
      (Delegation.Caller.startClock caller < event.1 ∧ event.1 ≤ Delegation.Caller.finishClock caller))
      (before i) (after i) := by
    simpa only [clocks.2, start] using current i
  obtain ⟨worker, present, same, grouped, history⟩ :=
    caller_cycle_worker_history effects.requests called cycle currentCall
  obtain ⟨_, _, only⟩ := Delegation.Requests.Proofs.unique_fulfillment effects.requests.fulfilled
    effects.requests.invocations.1 (List.mem_map.mpr ⟨caller, called, rfl⟩)
  have equal : worker = rows i :=
    (only worker ⟨present, same⟩).trans
      (only (rows i) ⟨List.mem_of_mem_filter (members i), matched.2.1⟩).symm
  rw [equal] at grouped
  exact ⟨_, history, grouped⟩

end Airbender.UnifiedReduced.Caller.Proofs
