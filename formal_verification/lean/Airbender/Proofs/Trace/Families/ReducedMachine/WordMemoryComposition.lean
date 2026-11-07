import Airbender.Proofs.ReducedMachine.NativeWordMemoryRetirement
import Airbender.Proofs.Trace.Families.ReducedMachine.WordMemoryClauses
import Airbender.Proofs.Trace.ProjectedStatefulComposition
import Airbender.Proofs.Trace.ProjectedTerminal
import Airbender.Review.Trace.Families.ReducedMachine.WordMemoryExecution

namespace Airbender.ReducedMachine.NativeWordMemoryExecutionProofs
open Native NativeShadow Arithmetic Trace Verification Reference.RiscV.Sail Reference.Sail
open _root_.Sail.ArchSem
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Fetch, original stateful decoder replay and PC preparation/retirement follow
    actual initialized native transfers. All local interfaces are discharged. -/
theorem image_fetched_step [MemoryPlatform SailRV32.exception]
    {trace : Data mersenne31Modulus NativeReducedFamily} {setup : SparseDecoderSetup WordMemoryMode}
    {initial : State} {cells : List Cell} {seeds : List ShadowSeed} {count logCapacity : Nat}
    (image : wordMemoryDecoderSetupImage (NativeROM.state initial) count logCapacity = some setup)
    (inputs : ShadowImageBoundary (fixedData trace) (NativeROM.state initial) cells seeds)
    (accepted : Accepted (fixedData trace)) (decoded : WordMemoryDecodedTrace (fixedData trace) setup)
    (capacity : count ≤ 1048576) (isa : WordMemoryISA setup (NativeROM.state initial))
    (ordinary : WordMemoryOrdinaryCells cells)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ (fixedData trace).rows)
    {before after : State} {events : List MemoryAccess}
    (past : SailHistory cells (events.filter fun event => architecturalAddress event.2.1) (NativeROM.state initial) before)
    (current : SailHistory cells ((rowEvents (fixedData trace).memoryEpoch row).reverse.filter
      fun event => architecturalAddress event.2.1) before after) :
    StepWith wordMemoryDecoderFields wordMemoryClause setup.program (retiredState before row.start.word.toBitVec)
      (retiredState after row.finish.word.toBitVec) := by
  obtain ⟨entry,member,source,query,_,effects⟩ :=
    NativeShadowRangeProofs.image_word_memory_results image inputs accepted decoded row present
  have sourceHere := NativeWordMemoryHistoryProofs.entry_source_after_history inputs.architectural past image capacity member
  have canonical := Trace.Proofs.native_query_pc_word (by decide : limbBase < mersenne31Modulus) query
  change row.start.word = Word.ofBitVec entry.pc at canonical
  have pcWord : row.start.word.toBitVec = entry.pc := by rw [canonical,Word.ofBitVec_roundtrip]
  have configuration := NativeWordMemoryPlatformProofs.configuration_after_history isa member past
  have ordinaryAddress := NativeWordMemoryPlatformProofs.initialized_ordinary image inputs accepted decoded ordinary row present
  refine ⟨entry,member,Trace.Proofs.entry_source_retired_state_run sourceHere _,?_,?_⟩
  · simpa only [pcWord] using Trace.Proofs.retired_state_pc before row.start.word.toBitVec
  · cases row with
    | mk family w =>
      cases family
      have transfer := NativeWordMemoryTransferProofs.transfer (fixedData trace).memoryEpoch
        (accepted.constraints _ present) source.fields query inputs.architectural past current
      exact NativeWordMemoryRetirementProofs.local_row_retirement source.fields effects transfer configuration ordinaryAddress

/-- State matching derives terminal PC bounds from the actual final native
    numerical effect, or from the original public PC on an empty trace. -/
theorem image_terminal_pc_bound {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup WordMemoryMode} {initial : State} {cells : List Cell} {seeds : List ShadowSeed}
    {count logCapacity : Nat}
    (image : wordMemoryDecoderSetupImage initial count logCapacity = some setup)
    (inputs : ShadowImageBoundary (fixedData trace) initial cells seeds)
    (accepted : Accepted (fixedData trace)) (decoded : WordMemoryDecodedTrace (fixedData trace) setup) :
    (fixedData trace).terminal.word.Bounded := by
  have matched := accepted.states.mem_iff.mpr (List.mem_cons_self (l := (fixedData trace).rows.map Row.start))
  rcases List.mem_cons.mp matched with same | finished
  · rw [same]
    exact Trace.Proofs.initial_pc_bound (by decide) inputs.initial
  · obtain ⟨row,present,same⟩ := List.mem_map.mp finished
    rw [← same]
    obtain ⟨entry,_,_,_,_,effects⟩ := NativeShadowRangeProofs.image_word_memory_results image inputs accepted decoded row present
    exact effects.pcBound

/-- Full native matching supplies clock order/PC chain; constructed original
    source replay supplies fetched steps. All native shadow tokens stay matched. -/
theorem image_execution_soundness [MemoryPlatform SailRV32.exception]
    {trace : Data mersenne31Modulus NativeReducedFamily} {setup : SparseDecoderSetup WordMemoryMode}
    {initial : State} {cells : List Cell} {seeds : List ShadowSeed} {count logCapacity : Nat}
    (image : wordMemoryDecoderSetupImage (NativeROM.state initial) count logCapacity = some setup)
    (inputs : ShadowImageBoundary (fixedData trace) (NativeROM.state initial) cells seeds)
    (accepted : Accepted (fixedData trace)) (decoded : WordMemoryDecodedTrace (fixedData trace) setup)
    (aligned : ∀ cell ∈ cells, cell.Aligned) (capacity : count ≤ 1048576)
    (isa : WordMemoryISA setup (NativeROM.state initial)) (ordinary : WordMemoryOrdinaryCells cells) :
    WordMemoryRealizes setup.program (fixedData trace) (NativeROM.state initial) cells := by
  have clocks := NativeShadowProofs.shadow_clock_boundary (by decide) inputs
  obtain ⟨history,rows,nativeAfter,consistent,permutation,ordered,nativeHistory,matched,_,_,_⟩ :=
    NativeWordMemoryHistoryProofs.image_projected_history image inputs accepted decoded aligned capacity
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

end Airbender.ReducedMachine.NativeWordMemoryExecutionProofs
