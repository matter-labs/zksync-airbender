import Airbender.Review.Trace.UnifiedReduced.Paths.SpanComputedStoreGaps
import Airbender.Proofs.UnifiedReduced.PathSpanProjection
import Airbender.Proofs.UnifiedReduced.WordMemory
import Airbender.Proofs.UnifiedReduced.PathCalls

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Trace.Proofs Arithmetic Reference.RiscV.Sail Reference.Sail
set_option warningAsError true

/-- First actual native pointer values, used only in derived proof evidence. -/
def path_span_native_pointer_values [Fact p.Prime] {data : RequestTrace p}
    {program : List UnifiedReduced.ProgramEntry} (span : PathCompleteSpan data program)
    (rows : Fin span.span.callCount → Delegation.Row p) (register : BitVec 5) : BitVec 32 :=
  (readToken (rows (PathCompleteSpan.first span.span)).assignment
    (path_span_pointer_port span.span register)).word.toBitVec

/-- Internal output of syntactic gap checking. All real native gap events stay
    present; only their values on the exact finite protected domain are framed. -/
structure PathSpanProtectedGapEvidence [Fact p.Prime] {data : RequestTrace p}
    {program : List UnifiedReduced.ProgramEntry} (span : PathCompleteSpan data program)
    (rows : Fin span.span.callCount → Delegation.Row p) : Prop where
  pointerFrames : ∀ target : Fin span.span.callCount, 0 < target.val →
    ∀ register ∈ path_span_pointer_registers span.span,
      PathRegisterGapFrames data program
        (span.start (PathCompleteSpan.first span.span) + 4) (span.start target) register
  refreshes : ∀ i j : Fin span.span.callCount, j.val = i.val + 1 →
    ∀ edge ∈ data.windowSteps (span.start i + 4) (span.start j),
    ∀ address ∈ path_span_protected_addresses span.span (path_span_native_pointer_values span rows),
      edge.1.address = (Cell.ram address).addressCode → edge.2.value = edge.1.value

/-- The original readonly certificate has exactly the same pointer-frame part. -/
def PathSpanReadOnlyGaps.pointerGaps [Fact p.Prime] {data : RequestTrace p}
    {program : List UnifiedReduced.ProgramEntry} {span : PathCompleteSpan data program}
    (gaps : PathSpanReadOnlyGaps span) : PathSpanPointerGaps span := by
  constructor
  intro cut afterFirst beforeLast aligned notOwned
  obtain ⟨instruction, scope, _, frames⟩ := gaps.code cut afterFirst beforeLast aligned notOwned
  exact ⟨instruction, scope, frames⟩

def PathSpanComputedStoreGaps.pointerGaps [Fact p.Prime] {data : RequestTrace p}
    {program : List UnifiedReduced.ProgramEntry} {span : PathCompleteSpan data program}
    (gaps : PathSpanComputedStoreGaps span) : PathSpanPointerGaps span := by
  constructor
  intro cut afterFirst beforeLast aligned notOwned
  obtain ⟨instruction, scope, frames, _⟩ := gaps.code cut afterFirst beforeLast aligned notOwned
  exact ⟨instruction, scope, frames⟩

/-- Ordinary gap syntax and the span's own caller refreshes frame pointers,
    independently of whether a gap stores to disjoint scratch RAM. -/
theorem path_span_pointer_gap_frames [Fact p.Prime]
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    (span : PathCompleteSpan data program) (gaps : PathSpanPointerGaps span)
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
  · obtain ⟨instruction, scope, pointers⟩ := gaps.code cut afterLower
      (beforeUpper.trans targetLast) aligned owned
    exact .ordinary scope (pointers register member)

private theorem path_store_append_pointer_call [Fact p.Prime]
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

/-- All actual call pointer words follow from the derived syntactic frames;
    no literal or native pointer equality is a public algorithm premise. -/
theorem path_span_pointer_values_of_frames
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry} {initial : State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program initial ca oa cells)
    (span : PathCompleteSpan data program) (rows : Fin span.span.callCount → Delegation.Row babyBearModulus)
    (members : ∀ i, rows i ∈ data.workers.windowRows (span.start i) (span.start i + 4))
    (frames : ∀ target : Fin span.span.callCount, 0 < target.val →
      ∀ register ∈ path_span_pointer_registers span.span,
        PathRegisterGapFrames data program
          (span.start (PathCompleteSpan.first span.span) + 4) (span.start target) register)
    {register : BitVec 5} (pointer : register ∈ path_span_pointer_registers span.span) :
    ∀ i, (readToken (rows i).assignment (path_span_pointer_port span.span register)).word =
      Word.ofBitVec (path_span_native_pointer_values span rows register) := by
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
  intro target
  change (readToken (rows target).assignment port).word = Word.ofBitVec word.toBitVec
  by_cases zero : target.val = 0
  · have same : target = first := Fin.ext zero
    subst target
    exact canonical.symm
  have positive : 0 < target.val := by omega
  have gap := frames target positive register pointer
  have nonzero := (path_span_pointer_register_properties span.span pointer).1
  have different := (path_span_pointer_register_properties span.span pointer).2
  have extended := path_store_append_pointer_call gap (span.code target) different
  have targetRange := of_decide_eq_true (List.mem_filter.mp (members target)).2
  have lower := gap.ordered
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

/-- The existing arbitrary-pointer readonly variant supplies finite protected
    gap evidence without restricting any first native pointer value. -/
theorem path_span_readonly_gap_evidence [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {initial : State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : ProtocolContextInputs data initial ca oa cells program)
    (span : PathCompleteSpan data program) (gaps : PathSpanReadOnlyGaps span)
    (rows : Fin span.span.callCount → Delegation.Row p) : PathSpanProtectedGapEvidence span rows := by
  refine ⟨?_, ?_⟩
  · intro target positive register pointer
    exact path_span_pointer_gap_frames span (PathSpanReadOnlyGaps.pointerGaps gaps) target positive pointer
  · intro i j adjacent edge included address _ ram
    exact path_span_gap_ram_refreshes hp inverse accepted inputs span gaps adjacent edge included address ram

/-- Finite protected refresh evidence preserves a real gap read while retaining
    all timestamp-refresh and disjoint-store events in the same history. -/
theorem path_span_protected_gap_frame [Fact p.Prime]
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {cells : List Cell}
    {events : List MemoryAccess} {before after : State}
    (span : PathCompleteSpan data program) (rows : Fin span.span.callCount → Delegation.Row p)
    (evidence : PathSpanProtectedGapEvidence span rows)
    {i j : Fin span.span.callCount} (adjacent : j.val = i.val + 1)
    (history : SailHistory cells events before after)
    (permutation : events.Perm ((data.windowSteps (span.start i + 4) (span.start j)).map transferEvent))
    (address : BitVec 32)
    (protectedAddress : address ∈ path_span_protected_addresses span.span (path_span_native_pointer_values span rows))
    (aligned : address.toNat % 4 = 0) (allAligned : ∀ cell ∈ cells, cell.Aligned) {value : BitVec 32}
    (read : (Cell.ram address).read before = .ok value before) :
    (Cell.ram address).read after = .ok value after := by
  apply history_cell_frame_of_refresh history allAligned (.ram address) aligned ?_ read
  intro event included same
  obtain ⟨edge, member, rfl⟩ := List.mem_map.mp (permutation.mem_iff.mp included)
  have refresh := evidence.refreshes i j adjacent edge member address protectedAddress same
  simp only [transferEvent, refresh]


/-- Static protection depends only on the protocol's actual pointer registers. -/
theorem path_span_protected_addresses_congr (span : Delegation.Caller.HashSpan)
    (left right : BitVec 5 → BitVec 32)
    (same : ∀ register ∈ path_span_pointer_registers span, left register = right register) :
    path_span_protected_addresses span left = path_span_protected_addresses span right := by
  cases span with
  | blakeG reduced =>
    have state := same 10 (by simp [path_span_pointer_registers])
    have message := same 11 (by simp [path_span_pointer_registers])
    simp only [path_span_protected_addresses, state, message]
  | blakeRound flags =>
    have state := same 10 (by simp [path_span_pointer_registers])
    have message := same 11 (by simp [path_span_pointer_registers])
    simp only [path_span_protected_addresses, state, message]
  | keccak =>
    have pointer := same 11 (by simp [path_span_pointer_registers])
    simp only [path_span_protected_addresses, pointer]

/-- Public pointer computations bind the first actual worker pointer reads. -/
theorem path_span_computed_pointer_values
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry} {initial : State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program initial ca oa cells)
    (span : PathCompleteSpan data program) (gaps : PathSpanComputedStoreGaps span)
    (rows : Fin span.span.callCount → Delegation.Row babyBearModulus)
    (members : ∀ i, rows i ∈ data.workers.windowRows (span.start i) (span.start i + 4)) :
    ∀ register ∈ path_span_pointer_registers span.span,
      path_span_native_pointer_values span rows register = gaps.pointerValues register := by
  intro register pointer
  let first := PathCompleteSpan.first span.span
  obtain ⟨_, window⟩ := path_caller_window (by decide) (by decide) accepted inputs.publicProgram
    inputs.ordinaryProgram inputs.initialization (span.code first) (by have := span.aligned first; omega)
  have family := window.family (rows first) (by simpa using members first)
  have properties := path_span_pointer_port_properties span.span pointer (rows first) family
  have registerProperties := path_span_pointer_register_properties span.span pointer
  have unique : (data.machine.initialMemory.map MemoryToken.address).Nodup := by
    rw [image_addresses inputs.initialization]
    exact inputs.distinct
  have read : (readToken (rows first).assignment (path_span_pointer_port span.span register)).word =
      Word.ofBitVec (gaps.pointerValues register) := by
    apply path_caller_frame_read (by decide) (by decide) accepted inputs.publicProgram inputs.ordinaryProgram
      inputs.initialization unique (span.code first) (by have := span.aligned first; omega)
      registerProperties.1 registerProperties.2 _ (by simpa using members first) properties.1 properties.2.1
    intro tokens matching
    exact path_controller_dataflow_token (by decide) (by decide) accepted inputs.publicProgram inputs.ordinaryProgram
      inputs.initialization unique inputs.tables (gaps.pointerPreparation register pointer)
      registerProperties.1 (span.aligned first) (by simpa using matching)
  change (readToken (rows first).assignment (path_span_pointer_port span.span register)).word.toBitVec = _
  rw [read, Word.ofBitVec_roundtrip]

/-- Ordinary STORE metadata comes from its original public instruction. -/
theorem path_store_fields {immediate : BitVec 12} {stored source : BitVec 5}
    {fields : DecoderData UnifiedFamily}
    (decoded : Mixed.decoderFields (.STORE (immediate, .Regidx stored, .Regidx source, 4)) = some fields) :
    fields = ⟨.machine, source, stored, 0,
      Word.ofBitVec (SailRV32.Functions.sign_extend (m := 32) immediate), 262144, 0⟩ := by
  simp [Mixed.decoderFields, UnifiedReduced.decoderFields, Trace.decoderFields,
    UnifiedReduced.arithmeticFields, DecoderData.mapFamily] at decoded
  exact decoded.symm

/-- The source/base read is derived from the unique raw prefix token and the
    public dataflow computation, rather than a desired architectural read. -/
theorem path_store_source_word
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry} {initial : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {cut : Nat}
    {immediate : BitVec 12} {stored source : BitVec 5} {baseValue : BitVec 32}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program initial ca oa cells)
    (scope : PathInstructionPreparation data program cut (.STORE (immediate, .Regidx stored, .Regidx source, 4)))
    (nonzero : source ≠ 0) (flow : PathControllerDataflow data program (cut - 4) source baseValue)
    {w : Nat → ZMod babyBearModulus}
    (member : (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) ∈ data.machine.rows)
    (ordinary : (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) ∉ data.callers)
    (last : Delegation.Caller.startClock (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) + 4 = cut) :
    (readToken w importedConstraintsMemoryPorts[0]).word = Word.ofBitVec baseValue := by
  have unique : (data.machine.initialMemory.map MemoryToken.address).Nodup := by
    rw [image_addresses inputs.initialization]
    exact inputs.distinct
  have floor := path_controller_dataflow_after_initial flow
  obtain ⟨tokens, matching, present, tokenUnique⟩ := first_port_prefix_token (by decide) (by decide)
    accepted inputs.publicProgram inputs.initialization unique (by omega) member ordinary last
  have aligned := (machine_clock_facts (by decide) (by decide) accepted.toRequestChecks inputs.publicProgram member).1
  obtain ⟨token, included, address, word⟩ := path_controller_dataflow_token (by decide) (by decide)
    accepted inputs.publicProgram inputs.ordinaryProgram inputs.initialization unique inputs.tables flow
    nonzero (by omega) matching
  obtain ⟨entry, entryMember, query, _, encoding⟩ := path_instruction_entry (by decide) accepted
    inputs.ordinaryProgram scope member ordinary last
  have fields := (run_program_sources inputs.ordinaryProgram entry entryMember).fields
  rw [encoding] at fields
  have metadata := path_store_fields fields
  have indices := native_query_indices (by decide) query
  have sourceIndex : (w 5).val = source.toNat := by
    have first := indices.1
    change (w 5).val = entry.data.rs1.toNat at first
    rw [metadata] at first
    exact first
  have sourceAddress : (readToken w importedConstraintsMemoryPorts[0]).address = (Cell.register source).addressCode := by
    simp [readToken, MemoryAddress.code, importedConstraintsMemoryPorts, Cell.addressCode, sourceIndex]
  have equal := List.inj_on_of_nodup_map tokenUnique present included (sourceAddress.trans address.symm)
  exact (congrArg MemoryToken.word equal).trans word

/-- Native STORE arithmetic derives the exact public effective address. The
    initialized address bound and all source values come from accepted matching. -/
theorem path_store_effective_address
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry} {initial : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {cut : Nat}
    {immediate : BitVec 12} {stored source : BitVec 5} {baseValue : BitVec 32}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program initial ca oa cells)
    (scope : PathInstructionPreparation data program cut (.STORE (immediate, .Regidx stored, .Regidx source, 4)))
    (nonzero : source ≠ 0) (flow : PathControllerDataflow data program (cut - 4) source baseValue)
    {w : Nat → ZMod babyBearModulus}
    (member : (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) ∈ data.machine.rows)
    (ordinary : (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) ∉ data.callers)
    (last : Delegation.Caller.startClock (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) + 4 = cut) :
    importedConstraintsMemoryPorts[2].address.code w =
      (Cell.ram (baseValue + SailRV32.Functions.sign_extend (m := 32) immediate)).addressCode := by
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (importedConstraints data.machine.rom) importedConstraintsTimestampLookups)
  obtain ⟨entry, entryMember, query, _, encoding⟩ := path_instruction_entry (by decide) accepted
    inputs.ordinaryProgram scope member ordinary last
  have fields := (run_program_sources inputs.ordinaryProgram entry entryMember).fields
  rw [encoding] at fields
  have metadata := path_store_fields fields
  have flags := UnifiedReduced.Proofs.decoder_selectors (by decide) core
    (by rw [metadata]; change 262144 < 524288; decide) query
  have load : w 28 = 0 := by
    simpa [metadata, importedConstraintsDecoderColumns, Nat.testBit, Nat.shiftRight_eq_div_pow] using flags 17
  have store : w 29 = 1 := by
    simpa [metadata, importedConstraintsDecoderColumns, Nat.testBit, Nat.shiftRight_eq_div_pow] using flags 18
  have sourceWord := path_store_source_word accepted inputs scope nonzero flow member ordinary last
  have nativeSource : Word.mk (w 36).val (w 37).val = Word.ofBitVec baseValue := by
    simpa [readToken, MemoryToken.word, importedConstraintsMemoryPorts, MemoryPort.readCode, WordColumns.code]
      using sourceWord
  have immediateWord := native_query_immediate_word (by decide)
    (by rw [metadata]; exact Word.ofBitVec_bound _) query
  change Word.mk (w 8).val (w 9).val = entry.data.immediate at immediateWord
  rw [metadata] at immediateWord
  have effects := mixed_memory_effects accepted inputs
  have portMember : importedConstraintsMemoryPorts[2] ∈ machinePorts (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) := by
    rw [machine_ports_ordinary member ordinary]
    exact Array.getElem_mem (by change 2 < 3; decide)
  obtain ⟨cell, _, address, bounded⟩ := effects.addresses _ (mixed_machine_member member portMember)
  have addressWord : (importedConstraintsMemoryPorts[2].address.word w).Bounded := by
    rw [address_word (address := importedConstraintsMemoryPorts[2].address)
      (w := w) (cell := cell) (by exact address.symm)]
    exact bounded
  have addressBound : (Word.mk (w 44).val (w 45).val).Bounded := by
    simpa [MemoryAddress.word, importedConstraintsMemoryPorts, WordColumns.evaluate] using addressWord
  have effective := UnifiedReduced.Proofs.word_memory_address (by decide) true core load store
    (nativeSource.symm ▸ Word.ofBitVec_bound _) (immediateWord.symm ▸ Word.ofBitVec_bound _) addressBound
  change (Word.mk (w 44).val (w 45).val).toBitVec = _ at effective
  rw [nativeSource, immediateWord, Word.ofBitVec_roundtrip, Word.ofBitVec_roundtrip] at effective
  have canonical : Word.ofBitVec (baseValue + SailRV32.Functions.sign_extend (m := 32) immediate) =
      Word.mk (w 44).val (w 45).val := by
    rw [← effective]
    apply Word.eq_of_value (Word.ofBitVec_bound _) addressBound
    rw [Word.ofBitVec_value, Word.toBitVec_toNat addressBound]
  simp [MemoryAddress.code, importedConstraintsMemoryPorts, Cell.addressCode, store, pairCode, canonical]
  decide

/-- Every protected touch in a STORE cycle is a real read refresh. The actual
    write is retained at its derived disjoint effective address, for any payload. -/
theorem path_store_protected_row_refreshes
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry} {initial : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {cut : Nat}
    {immediate : BitVec 12} {stored source : BitVec 5} {baseValue : BitVec 32}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program initial ca oa cells)
    (scope : PathInstructionPreparation data program cut (.STORE (immediate, .Regidx stored, .Regidx source, 4)))
    (nonzero : source ≠ 0) (flow : PathControllerDataflow data program (cut - 4) source baseValue)
    {w : Nat → ZMod babyBearModulus}
    (member : (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) ∈ data.machine.rows)
    (ordinary : (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) ∉ data.callers)
    (last : Delegation.Caller.startClock (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily) + 4 = cut)
    {port : MemoryPort} (portMember : port ∈ machinePorts (⟨.machine, w⟩ : Trace.Row babyBearModulus UnifiedFamily))
    {address : BitVec 32} (different : baseValue + SailRV32.Functions.sign_extend (m := 32) immediate ≠ address)
    (ram : port.address.code w = (Cell.ram address).addressCode) :
    (writeToken importedConstraintsTraceColumns w port).value = (readToken w port).value := by
  rw [machine_ports_ordinary member ordinary] at portMember
  simp [Trace.Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts] at portMember
  rcases portMember with rfl | rfl | rfl
  · rfl
  · rfl
  · have effective := path_store_effective_address accepted inputs scope nonzero flow member ordinary last
    exact False.elim (different (Cell.ram.inj (cell_address_injective (effective.symm.trans ram))))


/-- Both admitted protected-gap forms are ordinary decoded instructions. -/
theorem path_protected_instruction_not_caller [Fact p.Prime]
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {cut : Nat}
    {protectedAddresses : List (BitVec 32)} {instruction : SailRV32.instruction}
    (form : PathRamProtectedInstruction data program cut protectedAddresses instruction) :
    Delegation.Caller.decoderFields instruction = none := by
  cases form with
  | readOnly form => exact path_ram_readonly_not_caller form
  | store => rfl

/-- Syntactic readonly or computed-disjoint STORE preserves every actual
    protected read token in this occurrence, including timestamp refreshes. -/
theorem path_protected_instruction_refreshes
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry} {initial : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {cut : Nat}
    {protectedAddresses : List (BitVec 32)} {instruction : SailRV32.instruction}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program initial ca oa cells)
    (scope : PathInstructionPreparation data program cut instruction)
    (form : PathRamProtectedInstruction data program cut protectedAddresses instruction) (aligned : cut % 4 = 0) :
    ∀ edge ∈ data.windowSteps (cut - 4) cut, ∀ address ∈ protectedAddresses,
      edge.1.address = (Cell.ram address).addressCode → edge.2.value = edge.1.value := by
  cases form with
  | readOnly form =>
    intro edge included address _ ram
    exact path_ram_readonly_refreshes (by decide) (by decide) accepted inputs.publicProgram inputs.ordinaryProgram
      inputs.initialization scope form aligned edge included address ram
  | store immediate stored source baseValue nonzero flow disjoint =>
    have empty := path_instruction_workers_empty (by decide) (by decide) accepted inputs.publicProgram
      inputs.ordinaryProgram inputs.initialization scope rfl aligned
    intro edge included address protectedAddress ram
    rcases List.mem_append.mp included with machine | worker
    · obtain ⟨row, selected, step⟩ := List.mem_flatMap.mp machine
      obtain ⟨member, range⟩ := List.mem_filter.mp selected
      have range := of_decide_eq_true range
      have clocks := machine_clock_facts (by decide) (by decide) accepted.toRequestChecks inputs.publicProgram member
      have startAligned := clocks.1
      have last : Delegation.Caller.startClock row + 4 = cut := by omega
      have ordinary := path_instruction_ordinary (by decide) accepted inputs.publicProgram inputs.ordinaryProgram
        scope rfl member last
      obtain ⟨port, present, rfl⟩ := List.mem_map.mp step
      cases row with
      | mk kind w =>
        cases kind
        apply path_store_protected_row_refreshes accepted inputs scope nonzero flow member ordinary last
          (by simpa using present) _ ram
        intro equal
        exact disjoint (equal.symm ▸ protectedAddress)
    · obtain ⟨row, selected, _⟩ := List.mem_flatMap.mp worker
      rw [empty] at selected
      cases selected

/-- Public ordinary gap syntax excludes delegation workers from the actual
    interval, even when an ordinary gap performs a disjoint RAM write. -/
theorem path_span_computed_gap_workers_empty
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry} {initial : State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program initial ca oa cells)
    (span : PathCompleteSpan data program) (gaps : PathSpanComputedStoreGaps span)
    {i j : Fin span.span.callCount} (adjacent : j.val = i.val + 1) :
    data.workers.windowRows (span.start i + 4) (span.start j) = [] := by
  have first := span.aligned i
  have last := span.aligned j
  have floor := path_controller_dataflow_after_initial (span.control i)
  have ascending := span.increasing (show i < j by change i.val < j.val; omega)
  have firstStart : span.start (PathCompleteSpan.first span.span) ≤ span.start i :=
    span.increasing.monotone (by change 0 ≤ i.val; omega)
  have lastStart : span.start j ≤ span.start (PathCompleteSpan.last span.span) :=
    span.increasing.monotone (by change j.val ≤ span.span.callCount - 1; have := j.isLt; omega)
  have requests := request_windows (by decide) (by decide) accepted.toRequestChecks inputs.publicProgram
    (by omega : (span.start i + 4) % 4 = 0) last (by omega : 2 ≤ span.start i + 4)
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro worker selected
  obtain ⟨caller, matched, _⟩ := requests.workerMatches worker selected
  have called := List.mem_of_mem_filter matched.1
  have member := List.mem_of_mem_filter called
  have range := of_decide_eq_true (List.mem_filter.mp matched.1).2
  have clocks := machine_clock_facts (by decide) (by decide) accepted.toRequestChecks inputs.publicProgram member
  have nativeAligned := clocks.1
  have after : span.start i + 8 ≤ Delegation.Caller.startClock caller + 4 := by omega
  have before : Delegation.Caller.startClock caller + 4 ≤ span.start j := by omega
  obtain ⟨instruction, scope, _, form⟩ := gaps.code (Delegation.Caller.startClock caller + 4)
    (by omega) (by omega) (by omega) (path_span_gap_no_owned_cut span adjacent after before)
  exact path_instruction_ordinary (by decide) accepted inputs.publicProgram inputs.ordinaryProgram scope
    (path_protected_instruction_not_caller form) member rfl called

/-- The public finite-address check derives refresh equality for every actual
    protected event throughout the real adjacent-call interval. -/
theorem path_span_computed_gap_refreshes
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry} {initial : State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program initial ca oa cells)
    (span : PathCompleteSpan data program) (gaps : PathSpanComputedStoreGaps span)
    {i j : Fin span.span.callCount} (adjacent : j.val = i.val + 1) :
    ∀ edge ∈ data.windowSteps (span.start i + 4) (span.start j),
    ∀ address ∈ path_span_protected_addresses span.span gaps.pointerValues,
      edge.1.address = (Cell.ram address).addressCode → edge.2.value = edge.1.value := by
  have first := span.aligned i
  have last := span.aligned j
  have empty := path_span_computed_gap_workers_empty accepted inputs span gaps adjacent
  have firstStart : span.start (PathCompleteSpan.first span.span) ≤ span.start i :=
    span.increasing.monotone (by change 0 ≤ i.val; omega)
  have lastStart : span.start j ≤ span.start (PathCompleteSpan.last span.span) :=
    span.increasing.monotone (by change j.val ≤ span.span.callCount - 1; have := j.isLt; omega)
  intro edge included address protectedAddress ram
  rcases List.mem_append.mp included with machine | worker
  · obtain ⟨row, selected, step⟩ := List.mem_flatMap.mp machine
    obtain ⟨member, range⟩ := List.mem_filter.mp selected
    have range := of_decide_eq_true range
    have clocks := machine_clock_facts (by decide) (by decide) accepted.toRequestChecks inputs.publicProgram member
    have nativeAligned := clocks.1
    have after : span.start i + 8 ≤ Delegation.Caller.startClock row + 4 := by omega
    have before : Delegation.Caller.startClock row + 4 ≤ span.start j := by omega
    obtain ⟨instruction, scope, _, form⟩ := gaps.code (Delegation.Caller.startClock row + 4)
      (by omega) (by omega) (by omega) (path_span_gap_no_owned_cut span adjacent after before)
    apply path_protected_instruction_refreshes accepted inputs scope form (by omega)
      edge _ address protectedAddress ram
    exact List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr
      ⟨row, List.mem_filter.mpr ⟨member, decide_eq_true (by omega)⟩, step⟩))
  · obtain ⟨worker, selected, _⟩ := List.mem_flatMap.mp worker
    rw [empty] at selected
    cases selected

/-- Computed public pointer/source flows and static finite disjointness produce
    the same internal evidence consumed by the readonly algorithm proof. -/
theorem path_span_computed_store_gap_evidence
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry} {initial : State}
    {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program initial ca oa cells)
    (span : PathCompleteSpan data program) (gaps : PathSpanComputedStoreGaps span)
    (rows : Fin span.span.callCount → Delegation.Row babyBearModulus)
    (members : ∀ i, rows i ∈ data.workers.windowRows (span.start i) (span.start i + 4)) :
    PathSpanProtectedGapEvidence span rows := by
  have same := path_span_protected_addresses_congr span.span
    (path_span_native_pointer_values span rows) gaps.pointerValues
    (path_span_computed_pointer_values accepted inputs span gaps rows members)
  refine ⟨?_, ?_⟩
  · intro target positive register pointer
    exact path_span_pointer_gap_frames span (PathSpanComputedStoreGaps.pointerGaps gaps) target positive pointer
  · intro i j adjacent edge included address protectedAddress ram
    rw [same] at protectedAddress
    exact path_span_computed_gap_refreshes accepted inputs span gaps adjacent edge included address protectedAddress ram

end Airbender.UnifiedReduced.Caller.Proofs
