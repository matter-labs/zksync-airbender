import Airbender.Review.Trace.UnifiedReduced.Paths.GapFrames
import Airbender.Proofs.UnifiedReduced.PathControllerDataflow

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Trace.Proofs Arithmetic Reference.RiscV.Sail Reference.Sail
set_option warningAsError true

/-- Public single-occurrence syntax derives the actual native GPR refresh. -/
theorem path_code_frame_refreshes [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {cut : Nat} {register : BitVec 5}
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (image : initialImage before cells = some data.machine.initialMemory)
    (scope : PathRegisterCodeFrame data program cut register) (nonzero : register ≠ 0)
    (aligned : cut % 4 = 0) :
    ∀ edge ∈ data.windowSteps (cut - 4) cut,
      edge.1.address = (Cell.register register).addressCode → edge.2.value = edge.1.value := by
  cases scope with
  | ordinary code form =>
    exact path_frame_refreshes hp inverse accepted publicProgram ordinaryProgram image code form nonzero aligned
  | caller code different =>
    exact path_caller_frame_refreshes hp inverse accepted publicProgram ordinaryProgram image code nonzero different aligned

/-- The public interval certificate covers every actual machine and worker
    transfer. Native request slots place workers in their own caller cycle. -/
theorem path_gap_frames_refreshes [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {lower upper : Nat} {register : BitVec 5}
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (image : initialImage before cells = some data.machine.initialMemory)
    (frames : PathRegisterGapFrames data program lower upper register) (nonzero : register ≠ 0) :
    ∀ edge ∈ data.windowSteps lower upper,
      edge.1.address = (Cell.register register).addressCode → edge.2.value = edge.1.value := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have requests := request_windows size inverse accepted.toRequestChecks publicProgram
    frames.lowerAligned frames.upperAligned (by have := frames.afterInitial; omega)
  intro edge included address
  rcases List.mem_append.mp included with machine | native
  · obtain ⟨row, selected, step⟩ := List.mem_flatMap.mp machine
    obtain ⟨member, range⟩ := List.mem_filter.mp selected
    have range := of_decide_eq_true range
    have clocks := machine_clock_facts size inverse accepted.toRequestChecks publicProgram member
    have startAligned := clocks.1
    have upperAligned := frames.upperAligned
    have code := frames.code (Delegation.Caller.startClock row + 4) (by omega) (by omega) (by omega)
    apply path_code_frame_refreshes hp inverse accepted publicProgram ordinaryProgram image code nonzero (by omega)
      edge _ address
    apply List.mem_append.mpr
    exact Or.inl (List.mem_flatMap.mpr ⟨row, List.mem_filter.mpr ⟨member, decide_eq_true (by omega)⟩, step⟩)
  · obtain ⟨worker, selected, step⟩ := List.mem_flatMap.mp native
    obtain ⟨caller, matched, _⟩ := requests.workerMatches worker selected
    have called := List.mem_of_mem_filter matched.1
    have member := List.mem_of_mem_filter called
    have range := of_decide_eq_true (List.mem_filter.mp matched.1).2
    have clocks := machine_clock_facts size inverse accepted.toRequestChecks publicProgram member
    have startAligned := clocks.1
    have upperAligned := frames.upperAligned
    have code := frames.code (Delegation.Caller.startClock caller + 4) (by omega) (by omega) (by omega)
    have write := matched.2.2.writes (path_native_control_port worker.family) (path_control_port_member worker)
    have normalized : worker.writeTime =
        (timeOfPair (worker.writeToken (path_native_control_port worker.family)).time).value := by
      cases worker with
      | mk family w => cases family <;> rfl
    have localWindow : worker ∈ data.workers.windowRows
        ((Delegation.Caller.startClock caller + 4) - 4) (Delegation.Caller.startClock caller + 4) := by
      apply List.mem_filter.mpr
      refine ⟨List.mem_of_mem_filter selected, decide_eq_true ?_⟩
      rw [normalized, write]
      omega
    apply path_code_frame_refreshes hp inverse accepted publicProgram ordinaryProgram image code nonzero (by omega)
      edge _ address
    exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨worker, localWindow, step⟩))

/-- Raw interval matching transports an arbitrary native value through public
    GPR frames. No canonical value or chosen initial pointer is required. -/
theorem path_gap_value_token [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {lower upper : Nat} {register : BitVec 5}
    {value : Nat} {tokens : List (MemoryToken p)}
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (image : initialImage before cells = some data.machine.initialMemory)
    (uniqueSeeds : (data.machine.initialMemory.map MemoryToken.address).Nodup)
    (frames : PathRegisterGapFrames data program lower upper register) (nonzero : register ≠ 0)
    (seedToken : ∀ start : List (MemoryToken p),
      (data.machine.initialMemory ++ (data.prefixSteps lower).map Prod.snd).Perm
        (start ++ (data.prefixSteps lower).map Prod.fst) →
      ∃ token ∈ start, token.address = (Cell.register register).addressCode ∧ token.value = value)
    (matching : (data.machine.initialMemory ++ (data.prefixSteps upper).map Prod.snd).Perm
      (tokens ++ (data.prefixSteps upper).map Prod.fst)) :
    ∃ token ∈ tokens, token.address = (Cell.register register).addressCode ∧ token.value = value := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have positive : 2 ≤ lower := by have := frames.afterInitial; omega
  have requests := request_binding size inverse accepted.toRequestChecks publicProgram
  have facts := mixed_memory_facts size inverse accepted publicProgram image requests
  obtain ⟨start, earlier, later⟩ := Transfer.split_at facts (lower - 1)
  have prefixMatching := earlier.matching
  rw [mixed_prefix_steps data (by omega)] at prefixMatching
  obtain ⟨source, sourceMember, sourceAddress, sourceValue⟩ := seedToken start prefixMatching
  obtain ⟨finish, window, _⟩ := Transfer.split_at later (upper - 1)
  change Transfer.Facts ⟨start, finish, Transfer.windowSteps (mixedData data) (lower - 1) (upper - 1)⟩ at window
  rw [← mixed_window_steps size inverse accepted.toRequestChecks publicProgram
    frames.lowerAligned frames.upperAligned positive frames.ordered] at window
  have keys := boundary_keys MemoryToken.address earlier.matching earlier.addresses
  have unique : (start.map MemoryToken.address).Nodup := keys.nodup_iff.mp uniqueSeeds
  have seed : ∀ token ∈ start, token.address = (Cell.register register).addressCode → token.value = value := by
    intro token present address
    exact (congrArg MemoryToken.value (List.inj_on_of_nodup_map unique present sourceMember
      (address.trans sourceAddress.symm))).trans sourceValue
  have refreshes := path_gap_frames_refreshes hp inverse accepted publicProgram ordinaryProgram image frames nonzero
  have values := Transfer.produced_cell_values window (Cell.register register).addressCode value seed
    (by intro edge present address read; exact (refreshes edge present address).trans read)
  have boundaryKeys := boundary_keys MemoryToken.address window.matching window.addresses
  obtain ⟨token, present, address⟩ := List.mem_map.mp
    (boundaryKeys.mem_iff.mp (List.mem_map.mpr ⟨source, sourceMember, rfl⟩))
  have atTarget : token.address = (Cell.register register).addressCode := address.trans sourceAddress
  have raw := values token (window.matching.mem_iff.mpr (List.mem_append.mpr (Or.inl present))) atTarget
  have complete := matching_at_next_cut size inverse accepted.toRequestChecks publicProgram
    frames.lowerAligned frames.upperAligned positive frames.ordered prefixMatching window.matching
  have permutation : finish.Perm tokens := by
    apply List.perm_iff_count.mpr
    intro cell
    have left := complete.count_eq cell
    have right := matching.count_eq cell
    simp only [List.count_append] at left right
    omega
  exact ⟨token, permutation.mem_iff.mp present, atTarget, raw⟩

/-- The same certificate derives actual raw reads within the interval, with
    arbitrary seed values retained as existential outputs of earlier calls. -/
theorem path_gap_read_value [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {lower upper : Nat} {register : BitVec 5}
    {value : Nat} {edge : MemoryToken p × MemoryToken p}
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (image : initialImage before cells = some data.machine.initialMemory)
    (uniqueSeeds : (data.machine.initialMemory.map MemoryToken.address).Nodup)
    (frames : PathRegisterGapFrames data program lower upper register) (nonzero : register ≠ 0)
    (seedToken : ∀ start : List (MemoryToken p),
      (data.machine.initialMemory ++ (data.prefixSteps lower).map Prod.snd).Perm
        (start ++ (data.prefixSteps lower).map Prod.fst) →
      ∃ token ∈ start, token.address = (Cell.register register).addressCode ∧ token.value = value)
    (included : edge ∈ data.windowSteps lower upper)
    (address : edge.1.address = (Cell.register register).addressCode) : edge.1.value = value := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have positive : 2 ≤ lower := by have := frames.afterInitial; omega
  have requests := request_binding size inverse accepted.toRequestChecks publicProgram
  have facts := mixed_memory_facts size inverse accepted publicProgram image requests
  obtain ⟨start, earlier, later⟩ := Transfer.split_at facts (lower - 1)
  have prefixMatching := earlier.matching
  rw [mixed_prefix_steps data (by omega)] at prefixMatching
  obtain ⟨source, sourceMember, sourceAddress, sourceValue⟩ := seedToken start prefixMatching
  obtain ⟨finish, window, _⟩ := Transfer.split_at later (upper - 1)
  change Transfer.Facts ⟨start, finish, Transfer.windowSteps (mixedData data) (lower - 1) (upper - 1)⟩ at window
  rw [← mixed_window_steps size inverse accepted.toRequestChecks publicProgram
    frames.lowerAligned frames.upperAligned positive frames.ordered] at window
  have keys := boundary_keys MemoryToken.address earlier.matching earlier.addresses
  have unique : (start.map MemoryToken.address).Nodup := keys.nodup_iff.mp uniqueSeeds
  have seed : ∀ token ∈ start, token.address = (Cell.register register).addressCode → token.value = value := by
    intro token present same
    exact (congrArg MemoryToken.value (List.inj_on_of_nodup_map unique present sourceMember
      (same.trans sourceAddress.symm))).trans sourceValue
  have refreshes := path_gap_frames_refreshes hp inverse accepted publicProgram ordinaryProgram image frames nonzero
  exact Transfer.read_cell_values window (Cell.register register).addressCode value seed
    (by intro one present same read; exact (refreshes one present same).trans read) edge included address

end Airbender.UnifiedReduced.Caller.Proofs
