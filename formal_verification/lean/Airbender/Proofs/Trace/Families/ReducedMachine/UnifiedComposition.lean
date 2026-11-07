import Airbender.Proofs.ReducedMachine.NativeUnifiedExecution
import Airbender.Proofs.ReducedMachine.NativeWordMemoryTransfers
import Airbender.Proofs.Trace.Families.ReducedMachine.UnifiedAddressDomains
import Airbender.Proofs.Trace.Families.ReducedMachine.UnifiedProjectedHistory
import Airbender.Proofs.Trace.Platform
import Airbender.Proofs.Trace.ProjectedStatefulComposition
import Airbender.Proofs.Trace.ProjectedTerminal
import Airbender.Review.Trace.Families.ReducedMachine.UnifiedExecution

namespace Airbender.ReducedMachine.NativeUnifiedExecutionProofs
open Native NativeShadow Arithmetic Trace Verification Reference.RiscV.Sail Reference.Sail
open _root_.Sail.ArchSem
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Actual original public construction and common initialized ranges discharge
    operation-specific final-PC bounds, including control flow and native wrap. -/
theorem image_row_pc_bound {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup UnifiedMode} {initial : State} {cells : List Cell} {seeds : List ShadowSeed}
    {count logCapacity : Nat}
    (image : unifiedDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ShadowImageBoundary (fixedData trace) initial cells seeds)
    (accepted : Accepted (fixedData trace)) (decoded : UnifiedDecodedTrace (fixedData trace) setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ (fixedData trace).rows) :
    row.finish.word.Bounded := by
  obtain ⟨entry,member,source,query⟩ := NativeUnifiedDecoderProofs.trace_decoding image accepted decoded row present
  have native := accepted.constraints row present
  have ranges := (NativeUnifiedRangeProofs.image_value_bounds image inputs accepted decoded).1 row present
  cases row with
  | mk family w =>
    cases family
    have left := ranges importedConstraintsMemoryPorts[0] (by
      change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts])
    have right := ranges importedConstraintsMemoryPorts[1] (by
      change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts])
    rw [Trace.Proofs.read_word] at left right
    change (sourceWord w).Bounded at left
    change (registerOperandWord w).Bounded at right
    change (finalPCWord w).Bounded
    have canonical := Trace.Proofs.native_query_pc_word (by decide : limbBase < mersenne31Modulus) query
    change initialPCWord w = Word.ofBitVec entry.pc at canonical
    have aligned : (initialPCWord w).lo%4 = 0 := by
      rw [canonical]
      exact (Trace.Proofs.run_sparse_setup_sources image member).2
    rcases NativeUnifiedDecoderProofs.entry_profile source.fields with
      ⟨selected,pc,bits,instruction,fields,_,same⟩ | ⟨selected,_,_,_,fields,_,same⟩
    · have fetched : selected.SourceWith initial supportedDecoderFields :=
        ⟨by simpa only [pc,bits] using source.bytes,
          by simpa only [bits,instruction] using source.decoded,fields⟩
      exact NativeSupportedLocalProofs.selected_pc_bound (w := w) (entry := selected) (initial := initial) native fetched
        (query.trans same.symm) left right aligned
    · exact (NativeWordMemoryResultProofs.decoded_result native fields
        (query.trans same.symm) left aligned).pcBound

/-- Original fetch, stateful replay, preparation and normal retirement at the
    ACTUAL common projected states. Every local profile/CSR/read/result is derived. -/
theorem image_fetched_step [MemoryPlatform SailRV32.exception]
    {trace : Data mersenne31Modulus NativeReducedFamily} {setup : SparseDecoderSetup UnifiedMode}
    {initial : State} {cells : List Cell} {seeds : List ShadowSeed} {count logCapacity : Nat}
    (image : unifiedDecoderSetupImage (NativeROM.state initial) count logCapacity = some setup)
    (inputs : ShadowImageBoundary (fixedData trace) (NativeROM.state initial) cells seeds)
    (accepted : Accepted (fixedData trace)) (decoded : UnifiedDecodedTrace (fixedData trace) setup)
    (capacity : count ≤ 1048576) (isa : UnifiedISA setup (NativeROM.state initial))
    (ordinary : UnifiedOrdinaryCells setup cells)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ (fixedData trace).rows)
    {before after : State} {events : List MemoryAccess}
    (past : SailHistory cells (events.filter fun event => architecturalAddress event.2.1) (NativeROM.state initial) before)
    (current : SailHistory cells ((rowEvents (fixedData trace).memoryEpoch row).reverse.filter
      fun event => architecturalAddress event.2.1) before after) :
    StepWith unifiedDecoderFields unifiedClause setup.program (retiredState before row.start.word.toBitVec)
      (retiredState after row.finish.word.toBitVec) := by
  obtain ⟨entry,member,source,query⟩ := NativeUnifiedDecoderProofs.trace_decoding image accepted decoded row present
  have sourceHere := NativeUnifiedHistoryProofs.entry_source_after_history inputs.architectural past image capacity member
  have canonical := Trace.Proofs.native_query_pc_word (by decide : limbBase < mersenne31Modulus) query
  change row.start.word = Word.ofBitVec entry.pc at canonical
  have pcWord : row.start.word.toBitVec = entry.pc := by rw [canonical,Word.ofBitVec_roundtrip]
  have ranges := (NativeUnifiedRangeProofs.image_value_bounds image inputs accepted decoded).1 row present
  refine ⟨entry,member,Trace.Proofs.entry_source_retired_state_run sourceHere _,?_,?_⟩
  · simpa only [pcWord] using Trace.Proofs.retired_state_pc before row.start.word.toBitVec
  · cases row with
    | mk family w =>
      cases family
      have native := accepted.constraints _ present
      have left := ranges importedConstraintsMemoryPorts[0] (by
        change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts])
      have right := ranges importedConstraintsMemoryPorts[1] (by
        change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts])
      rw [Trace.Proofs.read_word] at left right
      have aligned : (initialPCWord w).lo%4 = 0 := by
        change initialPCWord w = Word.ofBitVec entry.pc at canonical
        rw [canonical]
        exact (Trace.Proofs.run_sparse_setup_sources image member).2
      rcases NativeUnifiedDecoderProofs.entry_profile source.fields with
        ⟨selected,pc,bits,instruction,fields,_,same⟩ | ⟨selected,_,_,instruction,fields,_,same⟩
      · have fetched : selected.SourceWith (NativeROM.state initial) supportedDecoderFields :=
          ⟨by simpa only [pc,bits] using source.bytes,
            by simpa only [bits,instruction] using source.decoded,fields⟩
        have history := current
        rw [supported_events native fields (query.trans same.symm) (fixedData trace).memoryEpoch] at history
        have csrs := Trace.Proofs.sail_history_control_flow_csrs past
        have readable : InstructionUsesMisa selected.instruction → ∃ value, before.regs.get? .misa = some value := by
          intro shape
          obtain ⟨value,read⟩ := isa.control ⟨entry,member,by simpa only [instruction] using shape⟩
          exact ⟨value,csrs.1.trans read⟩
        have configuration : (∃ args, selected.instruction = .JALR args) →
            before.regs.get? .cur_privilege = some .Machine ∧ ∃ security,
              before.regs.get? .mseccfg = some security ∧ SailRV32.Functions._get_Seccfg_MLPE security = 0 := by
          intro shape
          obtain ⟨privilege,security,read,disabled⟩ := isa.indirect ⟨entry,member,by simpa only [instruction] using shape⟩
          exact ⟨csrs.2.1.trans privilege,security,csrs.2.2.trans read,disabled⟩
        obtain ⟨clause,dispatch,execute⟩ := NativeSupportedLocalProofs.local_row_execution native fetched
          (query.trans same.symm) left right aligned (fixedData trace).memoryEpoch history readable configuration
        exact ⟨clause,by simpa only [instruction] using (supported_dispatch fields).trans dispatch,execute⟩
      · have activated : ∃ entry ∈ setup.program, InstructionUsesWordMemory entry.instruction :=
          ⟨entry,member,by simpa only [instruction] using memory_instruction fields⟩
        have configuration := Trace.Proofs.sail_history_configuration past (isa.memory activated)
        have ordinaryAddress := NativeUnifiedAddressProofs.initialized_ordinary inputs accepted (ordinary activated)
          ⟨.reduced,w⟩ present fields (query.trans same.symm)
        have effects := NativeWordMemoryResultProofs.decoded_result native fields (query.trans same.symm) left aligned
        have transfer := NativeWordMemoryTransferProofs.transfer (fixedData trace).memoryEpoch native fields
          (query.trans same.symm) inputs.architectural past current
        obtain ⟨clause,dispatch,execute⟩ := NativeWordMemoryRetirementProofs.local_row_retirement fields effects
          transfer configuration ordinaryAddress
        exact ⟨clause,by simpa only [instruction] using (memory_dispatch fields).trans dispatch,execute⟩

/-- Actual state matching derives the terminal bound from an operation-specific
    native final PC, or the original public initial PC when the trace is empty. -/
theorem image_terminal_pc_bound {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup UnifiedMode} {initial : State} {cells : List Cell} {seeds : List ShadowSeed}
    {count logCapacity : Nat}
    (image : unifiedDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ShadowImageBoundary (fixedData trace) initial cells seeds)
    (accepted : Accepted (fixedData trace)) (decoded : UnifiedDecodedTrace (fixedData trace) setup) :
    (fixedData trace).terminal.word.Bounded := by
  have matched := accepted.states.mem_iff.mpr (List.mem_cons_self (l := (fixedData trace).rows.map Row.start))
  rcases List.mem_cons.mp matched with same | finished
  · rw [same]
    exact Trace.Proofs.initial_pc_bound (by decide) inputs.initial
  · obtain ⟨row,present,same⟩ := List.mem_map.mp finished
    rw [← same]
    exact image_row_pc_bound image inputs accepted decoded row present

/-- Full native matching supplies clock order/PC chain; constructed original
    source replay supplies fetched steps. All native shadow tokens stay matched. -/
theorem image_execution_soundness [MemoryPlatform SailRV32.exception]
    {trace : Data mersenne31Modulus NativeReducedFamily} {setup : SparseDecoderSetup UnifiedMode}
    {initial : State} {cells : List Cell} {seeds : List ShadowSeed} {count logCapacity : Nat}
    (image : unifiedDecoderSetupImage (NativeROM.state initial) count logCapacity = some setup)
    (inputs : ShadowImageBoundary (fixedData trace) (NativeROM.state initial) cells seeds)
    (accepted : Accepted (fixedData trace)) (decoded : UnifiedDecodedTrace (fixedData trace) setup)
    (aligned : ∀ cell ∈ cells, cell.Aligned) (capacity : count ≤ 1048576)
    (isa : UnifiedISA setup (NativeROM.state initial)) (ordinary : UnifiedOrdinaryCells setup cells) :
    UnifiedRealizes setup.program (fixedData trace) (NativeROM.state initial) cells := by
  have clocks := NativeShadowProofs.shadow_clock_boundary (by decide) inputs
  obtain ⟨history,rows,nativeAfter,consistent,permutation,ordered,nativeHistory,matched,_,_,_⟩ :=
    NativeUnifiedHistoryProofs.image_projected_history image inputs accepted decoded aligned capacity
  have chain := Trace.Proofs.ordered_row_boundaries (by decide) accepted clocks permutation ordered
  have events : (rows.flatMap fun row => (rowEvents (fixedData trace).memoryEpoch row).reverse).Perm
      (fixedData trace).nativeEvents := by
    rw [Trace.Proofs.native_events_projection (by decide) accepted clocks]
    exact permutation.flatMap (fun row _ => List.reverse_perm _)
  have pc := Trace.Proofs.initial_state_pc (by decide) inputs.initial
  have step := fun row present {before after events} (_native : ∀ event ∈ events, event ∈ (fixedData trace).nativeEvents)
      past current => image_fetched_step image inputs accepted decoded capacity isa ordinary row present
        (before := before) (after := after) (events := events) past current
  have execution := Trace.Proofs.compose_projected_rows_run architecturalAddress pc step rows (fixedData trace).terminal
    (fun row member => permutation.mem_iff.mp member)
    (fun event member => events.mem_iff.mp member) chain nativeHistory
  exact Trace.Proofs.projected_trace_postconditions (by decide) accepted clocks architecturalAddress
    (NativeShadowProofs.shadow_image_projection inputs) (NativeShadowProofs.shadow_image_unique inputs)
    pc consistent chain nativeHistory matched execution

end Airbender.ReducedMachine.NativeUnifiedExecutionProofs
