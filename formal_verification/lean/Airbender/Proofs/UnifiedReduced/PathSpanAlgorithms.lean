import Airbender.Proofs.UnifiedReduced.PathSpanStoreFrames
import Airbender.Proofs.UnifiedReduced.PathSpanNativeViews
import Airbender.Proofs.Blake2Round.CompressionBinding
import Airbender.Proofs.Keccak.CallPermutation

namespace Airbender.UnifiedReduced.Caller.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail Reference.Sail Delegation.Proofs
set_option warningAsError true
set_option Elab.async false

private theorem path_row_of_family {row : Delegation.Row p} {family : Delegation.Family}
    (same : row.family = family) : row = ⟨family, row.assignment⟩ := by
  cases row
  cases same
  rfl

private theorem path_pointer_read {w : Nat → ZMod p} {cells : List Cell} {before after : State}
    {port : MemoryPort} {register : BitVec 5} {value : BitVec 32}
    (observed : ∃ cell ∈ cells, cell.addressCode = port.address.code w ∧
      cell.read before = .ok (memoryWord (port.readCode w)) before ∧
      cell.read after = .ok (memoryWord (port.writeCode w)) after)
    (address : port.address.code w = (Cell.register register).addressCode)
    (word : (readToken w port).word = Word.ofBitVec value) :
    (Cell.register register).read before = .ok value before := by
  obtain ⟨cell, _, code, read, _⟩ := observed
  have same := cell_address_injective (code.trans address)
  subst cell
  change (Cell.register register).read before = .ok (readToken w port).word.toBitVec before at read
  simpa only [word, Word.ofBitVec_roundtrip] using read

private theorem path_interleaved_constant {α : Type*} {count : Nat} (positive : 0 < count)
    (before after : Fin count → α) (calls : ∀ i, after i = before i)
    (gaps : ∀ i j, j.val = i.val + 1 → before j = after i) :
    ∀ i, before i = before ⟨0, positive⟩ ∧ after i = before ⟨0, positive⟩ := by
  have first : ∀ n, ∀ bound : n < count, before ⟨n, bound⟩ = before ⟨0, positive⟩ := by
    intro n
    induction n with
    | zero => intro bound; rfl
    | succ n ih =>
      intro bound
      have previous : n < count := by omega
      exact (gaps ⟨n, previous⟩ ⟨n + 1, bound⟩ rfl).trans
        ((calls ⟨n, previous⟩).trans (ih previous))
  intro i
  exact ⟨first i.val i.isLt, (calls i).trans (first i.val i.isLt)⟩

/-- Read back the existing logical endpoint view from the tracked physical
lanes. Scratch lanes remain internal to the native chain. -/
private theorem path_lanes_at {state : State} {pointer : BitVec 32} {cells : List Cell}
    (tracked : ∀ physical : Fin 31, ∀ half : Fin 2,
      Cell.ram (pointer + BitVec.ofNat 32 (8 * physical.val + 4 * half.val)) ∈ cells)
    (readable : ∀ cell ∈ cells, ∃ value, cell.read state = .ok value state) :
    Keccak.Permutation.LanesAt state pointer
      (Keccak.Proofs.logicalLanes 0 (Keccak.Proofs.physicalLanes state pointer)) := by
  intro lane
  let physical : Fin 31 := ⟨Keccak.Controller.physicalLane 0 lane,
    Nat.lt_trans (Keccak.Controller.Proofs.physical_bound 0 lane) (by decide)⟩
  obtain ⟨low, lowRead⟩ := readable _ (tracked physical 0)
  obtain ⟨high, highRead⟩ := readable _ (tracked physical 1)
  have lowRead : (Cell.ram (pointer + BitVec.ofNat 32 (Keccak.Permutation.laneOffset lane))).read state =
      .ok low state := by
    simpa only [physical, Keccak.Controller.physicalLane, Keccak.Permutation.laneOffset,
      Fin.val_zero, Nat.mul_zero, Nat.add_zero] using lowRead
  have four : BitVec.ofNat 32 4 = (4 : BitVec 32) := by decide +kernel
  have highRead : (Cell.ram (pointer + BitVec.ofNat 32 (Keccak.Permutation.laneOffset lane) + 4)).read state =
      .ok high state := by
    simpa only [physical, Keccak.Controller.physicalLane, Keccak.Permutation.laneOffset,
      Fin.val_one, Nat.mul_one, BitVec.ofNat_add, ← BitVec.add_assoc, four] using highRead
  have value : (Keccak.Proofs.logicalLanes 0 (Keccak.Proofs.physicalLanes state pointer))[lane] =
      low.toNat + 2 ^ 32 * high.toNat := by
    have view : (Keccak.Proofs.logicalLanes 0 (Keccak.Proofs.physicalLanes state pointer))[lane] =
        ramLane state (pointer + BitVec.ofNat 32 (Keccak.Permutation.laneOffset lane)) := by
      simp only [Keccak.Proofs.logicalLanes, Fin.getElem_fin, Vector.getElem_ofFn,
        Keccak.Proofs.physicalLanes, Keccak.Controller.physicalLane, Keccak.Permutation.laneOffset]
    rw [view, ramLane, ram_word_of_read lowRead, ram_word_of_read highRead]
  refine ⟨low, high, lowRead, highRead, value, ?_⟩
  rw [value]
  have := low.isLt
  have := high.isLt
  omega

/-- Complete actual indexed hash calls compose through the real ordinary gap
histories. Native matching derives every pointer, read, local transition and
protected view frame; this theorem accepts no desired result or projected trace.
The ordered history and event permutation are internal outputs of joint memory
matching in the public composed execution theorem. -/
private theorem path_span_algorithm_of_gap_evidence
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial finalState : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    {events : List MemoryAccess}
    (accepted : MixedMemoryAccepted data program)
    (inputs : MixedMemoryInputs data program initial ca oa cells)
    (span : PathCompleteSpan data program)
    (provide : ∀ rows : Fin span.span.callCount → Delegation.Row babyBearModulus,
      (∀ i, rows i ∈ data.workers.windowRows (span.start i) (span.start i + 4)) →
        PathSpanProtectedGapEvidence span rows)
    (order : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events initial finalState)
    (permutation : events.Perm (data.mixedSteps.map transferEvent)) :
    PathSpanAlgorithmAt span cells events initial := by
  classical
  let context : ProtocolContextInputs data initial ca oa cells program :=
    ⟨inputs.publicProgram, inputs.ordinaryProgram, inputs.initialization, inputs.distinct,
      inputs.aligned, inputs.setup, inputs.tables⟩
  obtain ⟨rows, _, members, _⟩ := path_complete_span_actual (by decide) (by decide) accepted context span
  have gapEvidence := provide rows (fun i => (members i).1)
  have nativeMembers (i : Fin span.span.callCount) : rows i ∈ data.workers.rows :=
    List.mem_of_mem_filter (members i).1
  obtain ⟨before, after, cuts, gapHistories⟩ := path_span_cut_states span order history
  have locals := path_span_local_histories accepted inputs span rows (fun i => (members i).1)
    permutation before after (fun i => (cuts i).2)
  choose localEvents localHistory localPermutation using locals
  have beforeReadable (i : Fin span.span.callCount) := path_prefix_readable inputs (cuts i).1
  have afterReadable (i : Fin span.span.callCount) :=
    history_cells_readable (cuts i).2 inputs.aligned (beforeReadable i)
  have gapValues (i j : Fin span.span.callCount) (adjacent : j.val = i.val + 1)
      (address : BitVec 32) (tracked : Cell.ram address ∈ cells)
      (protectedAddress : address ∈ path_span_protected_addresses span.span
        (path_span_native_pointer_values span rows)) :
      ramWord (before j) address = ramWord (after i) address := by
    have firstAligned := span.aligned i
    have lastAligned := span.aligned j
    have ascending := span.increasing (show i < j by change i.val < j.val; omega)
    have bounds : span.start i + 4 ≤ span.start j := by omega
    have selected := path_window_events_permutation (by decide) (by decide)
      accepted.toRequestChecks inputs.publicProgram
      (by omega : (span.start i + 4) % 4 = 0) lastAligned
      (by omega : 2 ≤ span.start i + 4) bounds permutation
    obtain ⟨value, read⟩ := afterReadable i _ tracked
    have retained := path_span_protected_gap_frame span rows gapEvidence adjacent
      (gapHistories i j adjacent) selected address protectedAddress (inputs.aligned _ tracked) inputs.aligned read
    rw [ram_word_of_read retained, ram_word_of_read read]
  have gapBlocks (i j : Fin span.span.callCount) (adjacent : j.val = i.val + 1)
      (pointer : BitVec 32) (n offset : Nat)
      (tracked : ∀ word : Fin n,
        Cell.ram (pointer + BitVec.ofNat 32 (4 * (offset + word.val))) ∈ cells)
      (protectedBlock : ∀ word : Fin n,
        pointer + BitVec.ofNat 32 (4 * (offset + word.val)) ∈
          path_span_protected_addresses span.span (path_span_native_pointer_values span rows)) :
      Blake2Round.Proofs.blockWords (before j) pointer n offset =
        Blake2Round.Proofs.blockWords (after i) pointer n offset := by
    apply Vector.ext
    intro word bound
    simp only [Blake2Round.Proofs.blockWords, Vector.getElem_ofFn, ramEncoding]
    rw [gapValues i j adjacent _ (tracked ⟨word, bound⟩) (protectedBlock ⟨word, bound⟩)]
  have result : PathSpanAlgorithmResult span.span
      (before (PathCompleteSpan.first span.span)) (after (PathCompleteSpan.last span.span)) := by
    rcases span with ⟨family, start, increasing, aligned, code, control, gFrames⟩
    cases family with
    | blakeG reduced =>
      let span : PathCompleteSpan data program :=
        ⟨.blakeG reduced, start, increasing, aligned, code, control, gFrames⟩
      let first := PathCompleteSpan.first span.span
      let last := PathCompleteSpan.last span.span
      let assignments := fun i : Fin (Blake2G.callCount reduced) => (rows i).assignment
      have typed (i : Fin (Blake2G.callCount reduced)) :
          rows i = (⟨.blakeG, assignments i⟩ : Delegation.Row babyBearModulus) :=
        path_row_of_family (members i).2.1
      have present (i : Fin (Blake2G.callCount reduced)) :
          (⟨.blakeG, assignments i⟩ : Delegation.Row babyBearModulus) ∈ data.workers.rows :=
        by simpa only [← typed i] using nativeMembers i
      have bound (i : Fin (Blake2G.callCount reduced)) :
          (readToken (assignments i) Blake2G.importedConstraintsMemoryPorts[8]).word =
            Blake2G.controlAt reduced i.val := (members i).2.2
      let state := path_span_native_pointer_values span rows 10
      let message := path_span_native_pointer_values span rows 11
      have stateWords := path_span_pointer_values_of_frames accepted inputs span rows
        (fun i => (members i).1) gapEvidence.pointerFrames (register := 10) (by simp [span, path_span_pointer_registers])
      have messageWords := path_span_pointer_values_of_frames accepted inputs span rows
        (fun i => (members i).1) gapEvidence.pointerFrames (register := 11) (by simp [span, path_span_pointer_registers])
      have pointers (i : Fin (Blake2G.callCount reduced)) :
          Blake2G.Native.statePointer (assignments i) = Word.ofBitVec state ∧
          Blake2G.Native.messagePointer (assignments i) = Word.ofBitVec message :=
        ⟨by
            have actual := stateWords i
            change (readToken (assignments i) Blake2G.importedConstraintsMemoryPorts[0]).word =
              Word.ofBitVec state at actual
            exact actual,
          by
            have actual := messageWords i
            change (readToken (assignments i) Blake2G.importedConstraintsMemoryPorts[5]).word =
              Word.ofBitVec message at actual
            exact actual⟩
      have tracked := g_native_tracking assignments accepted inputs present bound pointers
      have seed := path_g_index_zero_pointer_separation accepted inputs (present first) (bound first)
      have separate : state ≠ message := by
        simpa only [(pointers first).1, (pointers first).2, Word.ofBitVec_roundtrip] using seed
      have separations (i : Fin (Blake2G.callCount reduced)) : PathGPointerBinding ⟨.blakeG, assignments i⟩ := by
        simpa only [PathGPointerBinding, (pointers i).1, (pointers i).2,
          Word.ofBitVec_roundtrip] using separate
      have transitions (i : Fin (Blake2G.callCount reduced)) :=
        g_native_view_step i accepted inputs (present i) (bound i) (pointers i) (separations i) tracked
          (cuts i).1 (localHistory i) (by simpa only [← typed i] using localPermutation i)
      have stateTracked (word : Fin 16) :
          Cell.ram (state + BitVec.ofNat 32 (4 * (0 + word.val))) ∈ cells := by
        simpa using tracked true word
      have messageTracked (word : Fin 16) :
          Cell.ram (message + BitVec.ofNat 32 (4 * (0 + word.val))) ∈ cells := by
        simpa using tracked false word
      have stateProtected (word : Fin 16) : state + BitVec.ofNat 32 (4 * (0 + word.val)) ∈
          path_span_protected_addresses span.span (path_span_native_pointer_values span rows) := by
        apply List.mem_append.mpr
        exact Or.inl (List.mem_map.mpr ⟨word.val, List.mem_range.mpr word.isLt, by simp only [Nat.zero_add, state]⟩)
      have messageProtected (word : Fin 16) : message + BitVec.ofNat 32 (4 * (0 + word.val)) ∈
          path_span_protected_addresses span.span (path_span_native_pointer_values span rows) := by
        apply List.mem_append.mpr
        exact Or.inr (List.mem_map.mpr ⟨word.val, List.mem_range.mpr word.isLt,
          by simp only [Nat.zero_add, message]⟩)
      have messageGaps (i j : Fin (Blake2G.callCount reduced)) (adjacent : j.val = i.val + 1) :
          Blake2G.Proofs.physicalWords (before j) message = Blake2G.Proofs.physicalWords (after i) message :=
        gapBlocks i j adjacent message 16 0 messageTracked messageProtected
      have messageConstant := path_interleaved_constant (path_span_call_count_positive (.blakeG reduced))
        (fun i => Blake2G.Proofs.physicalWords (before i) message)
        (fun i => Blake2G.Proofs.physicalWords (after i) message)
        (fun i => (transitions i).2) messageGaps
      have stateGaps (i j : Fin (Blake2G.callCount reduced)) (adjacent : j.val = i.val + 1) :
          (Blake2G.Proofs.physicalWords (before j) state).map Word.value =
            (Blake2G.Proofs.physicalWords (after i) state).map Word.value :=
        congrArg (fun vector : Vector Word 16 => vector.map Word.value)
          (gapBlocks i j adjacent state 16 0 stateTracked stateProtected)
      have calls (i : Fin (Blake2G.callCount reduced)) :
          (Blake2G.Proofs.physicalWords (after i) state).map Word.value =
            Blake2G.WorkVector.step reduced i.val (Blake2G.Proofs.physicalWords (before first) message)
              ((Blake2G.Proofs.physicalWords (before i) state).map Word.value) := by
        have current := (transitions i).1
        rw [(messageConstant i).1] at current
        exact current
      have folded := path_interleaved_view_fold (path_span_call_count_positive (.blakeG reduced))
        (fun i => (Blake2G.Proofs.physicalWords (before i) state).map Word.value)
        (fun i => (Blake2G.Proofs.physicalWords (after i) state).map Word.value)
        (fun index value => Blake2G.WorkVector.step reduced index
          (Blake2G.Proofs.physicalWords (before first) message) value) calls stateGaps
      have observed := path_worker_observations accepted inputs (present first)
        (cuts first).1 (localHistory first) (by simpa only [← typed first] using localPermutation first)
      have stateRead := path_pointer_read (observed Blake2G.importedConstraintsMemoryPorts[0] (Array.getElem_mem (by change 0 < 9; decide)))
        (register := 10) (by rfl) (stateWords first)
      have messageRead := path_pointer_read (observed Blake2G.importedConstraintsMemoryPorts[5] (Array.getElem_mem (by change 5 < 9; decide)))
        (register := 11) (by rfl) (messageWords first)
      refine ⟨state, message, Blake2G.Proofs.physicalWords (before first) state,
        Blake2G.Proofs.physicalWords (before first) message,
        Blake2G.Proofs.physicalWords (after last) state, ?_, ?_⟩
      · refine ⟨⟨stateRead, messageRead⟩,
          Blake2Round.Proofs.block_at stateTracked (beforeReadable first),
          Blake2Round.Proofs.block_at messageTracked (beforeReadable first),
          Blake2Round.Proofs.block_at stateTracked (afterReadable last), ?_⟩
        have unchanged : Blake2G.Proofs.physicalWords (after last) message =
            Blake2G.Proofs.physicalWords (before first) message := (messageConstant last).2
        rw [← unchanged]
        exact Blake2Round.Proofs.block_at messageTracked (afterReadable last)
      · exact folded
    | blakeRound flags =>
      let span : PathCompleteSpan data program :=
        ⟨.blakeRound flags, start, increasing, aligned, code, control, gFrames⟩
      let first := PathCompleteSpan.first span.span
      let last := PathCompleteSpan.last span.span
      let assignments := fun i : Fin span.span.callCount => (rows i).assignment
      have typed (i : Fin span.span.callCount) :
          rows i = (⟨.blakeRound, assignments i⟩ : Delegation.Row babyBearModulus) :=
        path_row_of_family (members i).2.1
      have present (i : Fin span.span.callCount) :
          (⟨.blakeRound, assignments i⟩ : Delegation.Row babyBearModulus) ∈ data.workers.rows :=
        by simpa only [← typed i] using nativeMembers i
      have bound (i : Fin span.span.callCount) :
          (readToken (assignments i) Blake2Round.importedConstraintsMemoryPorts[42]).word =
            Blake2Round.controlAt flags i.val := (members i).2.2
      let state := path_span_native_pointer_values span rows 10
      let message := path_span_native_pointer_values span rows 11
      have stateWords := path_span_pointer_values_of_frames accepted inputs span rows
        (fun i => (members i).1) gapEvidence.pointerFrames (register := 10) (by simp [span, path_span_pointer_registers])
      have messageWords := path_span_pointer_values_of_frames accepted inputs span rows
        (fun i => (members i).1) gapEvidence.pointerFrames (register := 11) (by simp [span, path_span_pointer_registers])
      have pointers (i : Fin span.span.callCount) :
          (Blake2Round.Native.input 0 (assignments i)).statePointer = Word.ofBitVec state ∧
          (Blake2Round.Native.input 0 (assignments i)).messagePointer = Word.ofBitVec message :=
        ⟨by
            have actual := stateWords i
            change (readToken (assignments i) Blake2Round.importedConstraintsMemoryPorts[0]).word =
              Word.ofBitVec state at actual
            exact actual,
          by
            have actual := messageWords i
            change (readToken (assignments i) Blake2Round.importedConstraintsMemoryPorts[25]).word =
              Word.ofBitVec message at actual
            exact actual⟩
      have tracked := round_native_tracking accepted inputs (present first) (pointers first)
      have stateTracked (word : Fin 8) :
          Cell.ram (state + BitVec.ofNat 32 (4 * (0 + word.val))) ∈ cells := by
        have actual := tracked ⟨word.val, by have := word.isLt; omega⟩
        simpa only [Fin.val_mk, if_pos (show word.val < 24 by have := word.isLt; omega), Nat.zero_add] using actual
      have extendedTracked (word : Fin 16) :
          Cell.ram (state + BitVec.ofNat 32 (4 * (8 + word.val))) ∈ cells := by
        have actual := tracked ⟨8 + word.val, by have := word.isLt; omega⟩
        simpa only [Fin.val_mk, if_pos (show 8 + word.val < 24 by have := word.isLt; omega)] using actual
      have messageTracked (word : Fin 16) :
          Cell.ram (message + BitVec.ofNat 32 (4 * (0 + word.val))) ∈ cells := by
        have actual := tracked ⟨24 + word.val, by have := word.isLt; omega⟩
        simpa only [Fin.val_mk, if_neg (show ¬ 24 + word.val < 24 by omega),
          Nat.add_sub_cancel_left, Nat.zero_add] using actual
      have stateProtected (word : Fin 8) : state + BitVec.ofNat 32 (4 * (0 + word.val)) ∈
          path_span_protected_addresses span.span (path_span_native_pointer_values span rows) := by
        apply List.mem_append.mpr
        exact Or.inl (List.mem_map.mpr ⟨word.val, List.mem_range.mpr (by have := word.isLt; omega),
          by simp only [Nat.zero_add, state]⟩)
      have extendedProtected (word : Fin 16) : state + BitVec.ofNat 32 (4 * (8 + word.val)) ∈
          path_span_protected_addresses span.span (path_span_native_pointer_values span rows) := by
        apply List.mem_append.mpr
        exact Or.inl (List.mem_map.mpr ⟨8 + word.val, List.mem_range.mpr (by have := word.isLt; omega), rfl⟩)
      have messageProtected (word : Fin 16) : message + BitVec.ofNat 32 (4 * (0 + word.val)) ∈
          path_span_protected_addresses span.span (path_span_native_pointer_values span rows) := by
        apply List.mem_append.mpr
        exact Or.inr (List.mem_map.mpr ⟨word.val, List.mem_range.mpr word.isLt,
          by simp only [Nat.zero_add, message]⟩)
      have transitions (i : Fin span.span.callCount) :=
        round_native_view_step flags i accepted inputs (present i) (bound i) (pointers i)
          (cuts i).1 (localHistory i) (by simpa only [← typed i] using localPermutation i)
      have messageGaps (i j : Fin span.span.callCount) (adjacent : j.val = i.val + 1) :
          Blake2Round.Proofs.blockWords (before j) message 16 0 =
            Blake2Round.Proofs.blockWords (after i) message 16 0 :=
        gapBlocks i j adjacent message 16 0 messageTracked messageProtected
      have messageConstant := path_interleaved_constant (path_span_call_count_positive span.span)
        (fun i => Blake2Round.Proofs.blockWords (before i) message 16 0)
        (fun i => Blake2Round.Proofs.blockWords (after i) message 16 0)
        (fun i => (transitions i).2) messageGaps
      have stateGaps (i j : Fin span.span.callCount) (adjacent : j.val = i.val + 1) :
          Blake2Round.Proofs.physicalState (before j) state =
            Blake2Round.Proofs.physicalState (after i) state := by
        apply Prod.ext
        · exact gapBlocks i j adjacent state 8 0 stateTracked stateProtected
        · exact gapBlocks i j adjacent state 16 8 extendedTracked extendedProtected
      have calls (i : Fin span.span.callCount) :
          Blake2Round.Proofs.physicalState (after i) state =
            Blake2Round.Compression.step flags (Fin.ofNat 10 i.val)
              (Blake2Round.Proofs.physicalState (before i) state)
              (Blake2Round.Proofs.blockWords (before first) message 16 0) := by
        have current := (transitions i).1
        rw [(messageConstant i).1] at current
        exact current
      have folded := path_interleaved_view_fold (path_span_call_count_positive span.span)
        (fun i => Blake2Round.Proofs.physicalState (before i) state)
        (fun i => Blake2Round.Proofs.physicalState (after i) state)
        (fun index value => Blake2Round.Compression.step flags (Fin.ofNat 10 index) value
          (Blake2Round.Proofs.blockWords (before first) message 16 0)) calls stateGaps
      have observed := path_worker_observations accepted inputs (present first)
        (cuts first).1 (localHistory first) (by simpa only [← typed first] using localPermutation first)
      have stateRead := path_pointer_read
        (observed Blake2Round.importedConstraintsMemoryPorts[0] (Array.getElem_mem (by change 0 < 43; decide)))
        (register := 10) (by rfl) (stateWords first)
      have messageRead := path_pointer_read
        (observed Blake2Round.importedConstraintsMemoryPorts[25] (Array.getElem_mem (by change 25 < 43; decide)))
        (register := 11) (by rfl) (messageWords first)
      refine ⟨state, message, Blake2Round.Proofs.physicalState (before first) state,
        Blake2Round.Proofs.physicalState (after last) state,
        Blake2Round.Proofs.blockWords (before first) message 16 0, ?_, ?_⟩
      · exact ⟨⟨stateRead, messageRead⟩,
          Blake2Round.Proofs.block_at stateTracked (beforeReadable first),
          Blake2Round.Proofs.block_at extendedTracked (beforeReadable first),
          Blake2Round.Proofs.block_at messageTracked (beforeReadable first),
          Blake2Round.Proofs.block_at stateTracked (afterReadable last),
          Blake2Round.Proofs.block_at extendedTracked (afterReadable last)⟩
      · exact folded
    | keccak =>
      let span : PathCompleteSpan data program := ⟨.keccak, start, increasing, aligned, code, control, gFrames⟩
      let first := PathCompleteSpan.first span.span
      let last := PathCompleteSpan.last span.span
      let assignments := fun i : Fin 649 => (rows i).assignment
      have typed (i : Fin 649) : rows i = (⟨.keccak, assignments i⟩ : Delegation.Row babyBearModulus) :=
        path_row_of_family (members i).2.1
      have present (i : Fin 649) : (⟨.keccak, assignments i⟩ : Delegation.Row babyBearModulus) ∈ data.workers.rows :=
        by simpa only [← typed i] using nativeMembers i
      have bound (i : Fin 649) : (readToken (assignments i) Keccak.importedConstraintsMemoryPorts[0]).word =
          ⟨(HashCallPosition.keccakControl i).packed, 0⟩ := (members i).2.2
      let pointer := path_span_native_pointer_values span rows 11
      have pointerWords := path_span_pointer_values_of_frames accepted inputs span rows
        (fun i => (members i).1) gapEvidence.pointerFrames (register := 11) (by simp [span, path_span_pointer_registers])
      have pointers (i : Fin 649) : Keccak.statePointer (assignments i) = Word.ofBitVec pointer := by
        have words := pointerWords i
        change (readToken (assignments i) Keccak.importedConstraintsMemoryPorts[1]).word = Word.ofBitVec pointer at words
        exact (Keccak.Call.Proofs.pointer_words (assignments i)).1.symm.trans words
      have tracked := keccak_native_tracking assignments accepted inputs present bound pointers
      have protectedWords (physical : Fin 31) (half : Fin 2) :
          pointer + BitVec.ofNat 32 (8 * physical.val + 4 * half.val) ∈
            path_span_protected_addresses span.span (path_span_native_pointer_values span rows) := by
        apply List.mem_map.mpr
        refine ⟨2 * physical.val + half.val, List.mem_range.mpr (by
          have := physical.isLt; have := half.isLt; omega), ?_⟩
        congr 2
        omega
      have transitions (i : Fin 649) :=
        keccak_native_view_step i accepted inputs (present i) (bound i) (pointers i) tracked
          (cuts i).1 (localHistory i) (by simpa only [← typed i] using localPermutation i)
      have laneGaps (i j : Fin 649) (adjacent : j.val = i.val + 1) :
          Keccak.Proofs.physicalLanes (before j) pointer = Keccak.Proofs.physicalLanes (after i) pointer := by
        funext physical
        change ramLane (before j) (pointer + BitVec.ofNat 32 (8 * physical.val)) =
          ramLane (after i) (pointer + BitVec.ofNat 32 (8 * physical.val))
        have lowTracked : Cell.ram (pointer + BitVec.ofNat 32 (8 * physical.val)) ∈ cells := by
          simpa only [Fin.val_zero, Nat.mul_zero, Nat.add_zero] using tracked physical 0
        have four : BitVec.ofNat 32 4 = (4 : BitVec 32) := by decide +kernel
        have highTracked : Cell.ram (pointer + BitVec.ofNat 32 (8 * physical.val) + 4) ∈ cells := by
          simpa only [Fin.val_one, Nat.mul_one, BitVec.ofNat_add,
            ← BitVec.add_assoc, four] using tracked physical 1
        have lowProtected : pointer + BitVec.ofNat 32 (8 * physical.val) ∈
            path_span_protected_addresses span.span (path_span_native_pointer_values span rows) := by
          simpa only [Fin.val_zero, Nat.mul_zero, Nat.add_zero] using protectedWords physical 0
        have highProtected : pointer + BitVec.ofNat 32 (8 * physical.val) + 4 ∈
            path_span_protected_addresses span.span (path_span_native_pointer_values span rows) := by
          simpa only [Fin.val_one, Nat.mul_one, BitVec.ofNat_add, ← BitVec.add_assoc, four]
            using protectedWords physical 1
        rw [ramLane, ramLane, gapValues i j adjacent _ lowTracked lowProtected,
          gapValues i j adjacent _ highTracked highProtected]
      obtain ⟨states, firstState, lastState, chain⟩ := path_interleaved_reverse_chain (by decide : 0 < 649)
        (fun i => Keccak.Proofs.physicalLanes (before i) pointer)
        (fun i => Keccak.Proofs.physicalLanes (after i) pointer)
        (fun index value => Keccak.Proofs.microStep (Fin.ofNat 649 index) value)
        (by
          intro i
          have same : Fin.ofNat 649 i.val = i := by
            apply Fin.ext
            exact Nat.mod_eq_of_lt i.isLt
          simpa only [same] using transitions i) laneGaps
      have pure := Keccak.Proofs.permutation_of_physical_chain states (by
        intro i
        have current := chain i
        have inRange : 648 - i.val < 649 := by omega
        have same : Fin.ofNat 649 (649 - 1 - i.val) = ⟨648 - i.val, inRange⟩ := by
          apply Fin.ext
          exact Nat.mod_eq_of_lt inRange
        simpa only [same] using current)
      have firstEndpoint : states (0 : Fin 650) =
          Keccak.Proofs.physicalLanes (after last) pointer := firstState
      have lastEndpoint : states (649 : Fin 650) =
          Keccak.Proofs.physicalLanes (before first) pointer := lastState
      rw [firstEndpoint, lastEndpoint] at pure
      have observed := path_worker_observations accepted inputs (present first)
        (cuts first).1 (localHistory first) (by simpa only [← typed first] using localPermutation first)
      have pointerRead := path_pointer_read
        (observed Keccak.importedConstraintsMemoryPorts[1] (Array.getElem_mem (by change 1 < 14; decide)))
        (register := 11) (by rfl) (pointerWords first)
      exact ⟨pointer, Keccak.Proofs.logicalLanes 0 (Keccak.Proofs.physicalLanes (before first) pointer),
        Keccak.Proofs.logicalLanes 0 (Keccak.Proofs.physicalLanes (after last) pointer),
        ⟨pointerRead, path_lanes_at tracked (beforeReadable first), path_lanes_at tracked (afterReadable last)⟩, pure⟩
  let first := PathCompleteSpan.first span.span
  let last := PathCompleteSpan.last span.span
  have bounds : span.start first ≤ span.start last + 4 := by
    have indices : first ≤ last := by change 0 ≤ _; omega
    have ascending := span.increasing.monotone indices
    omega
  obtain ⟨one, two, _, past, current, _⟩ := history_window order history bounds
  have firstState := sail_history_deterministic past (cuts first).1
  have actualLast := history_prefix_of_window order (by omega : span.start last ≤ span.start last + 4)
    (cuts last).1 (cuts last).2
  have selectedLast := history_prefix_of_window order bounds past current
  have lastState := sail_history_deterministic selectedLast actualLast
  exact ⟨before first, after last, (cuts first).1,
    by simpa only [firstState, lastState] using current, result⟩

/-- Existing arbitrary-pointer readonly gaps: all native occurrences and gap
refreshes are derived without constraining the initial pointer values. -/
theorem path_span_algorithm_at
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial finalState : State} {ca oa : List (BitVec 32)} {cells : List Cell} {events : List MemoryAccess}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program initial ca oa cells)
    (span : PathCompleteSpan data program) (gaps : PathSpanReadOnlyGaps span)
    (order : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events initial finalState)
    (permutation : events.Perm (data.mixedSteps.map transferEvent)) :
    PathSpanAlgorithmAt span cells events initial := by
  let context : ProtocolContextInputs data initial ca oa cells program :=
    ⟨inputs.publicProgram, inputs.ordinaryProgram, inputs.initialization, inputs.distinct,
      inputs.aligned, inputs.setup, inputs.tables⟩
  exact path_span_algorithm_of_gap_evidence accepted inputs span
    (fun rows _ => path_span_readonly_gap_evidence (by decide) (by decide) accepted context span gaps rows)
    order history permutation

/-- Public computed-address store certificates supply protected gap evidence.
Stores outside the protected blocks retain their complete real RAM effects. -/
theorem path_span_algorithm_at_computed_stores
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial finalState : State} {ca oa : List (BitVec 32)} {cells : List Cell} {events : List MemoryAccess}
    (accepted : MixedMemoryAccepted data program) (inputs : MixedMemoryInputs data program initial ca oa cells)
    (span : PathCompleteSpan data program) (gaps : PathSpanComputedStoreGaps span)
    (order : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events initial finalState)
    (permutation : events.Perm (data.mixedSteps.map transferEvent)) :
    PathSpanAlgorithmAt span cells events initial :=
  path_span_algorithm_of_gap_evidence accepted inputs span
    (fun rows members => path_span_computed_store_gap_evidence accepted inputs span gaps rows members)
    order history permutation

end Airbender.UnifiedReduced.Caller.Proofs
