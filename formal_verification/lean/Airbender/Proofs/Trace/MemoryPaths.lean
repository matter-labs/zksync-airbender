import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.Trace.Paths
import Mathlib.Data.List.Nodup

namespace Airbender.Trace.Proofs

variable {Kind : Type} [CircuitLayout Kind]

/-- A transfer keeps its address, so matching preserves the boundary address
    multiset. In particular, one initialized cell per address implies one final cell. -/
theorem boundary_keys {S K : Type} (key : S → K) {initial terminal : List S}
    {steps : List (S × S)}
    (matched : (initial ++ steps.map Prod.snd).Perm (terminal ++ steps.map Prod.fst))
    (preserved : ∀ edge ∈ steps, key edge.1 = key edge.2) :
    (initial.map key).Perm (terminal.map key) := by
  have mapped := matched.map key
  simp only [List.map_append, List.map_map, Function.comp_def] at mapped
  have same : steps.map (fun edge => key edge.2) = steps.map (fun edge => key edge.1) := by
    apply List.map_congr_left
    intro edge member
    exact (preserved edge member).symm
  rw [same] at mapped
  exact (List.perm_append_right_iff _).mp mapped

theorem key_filter_singleton {S K : Type} [DecidableEq K]
    (key : S → K) {states : List S} (unique : (states.map key).Nodup)
    {source : S} (member : source ∈ states) :
    states.filter (fun state => key state = key source) = [source] := by
  classical
  induction states with
  | nil => simp at member
  | cons first rest ih =>
    have both := List.nodup_cons.mp (by simpa only [List.map_cons] using unique)
    by_cases same : first = source
    · subst first
      have none : rest.filter (fun state => key state = key source) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro state stateMember
        have different : key state ≠ key source := by
          intro equal
          exact both.1 (List.mem_map.mpr ⟨state, stateMember, equal⟩)
        simp [different]
      simp [none]
    · have inRest : source ∈ rest := (List.mem_cons.mp member).resolve_left (Ne.symm same)
      have different : key first ≠ key source := by
        intro equal
        exact both.1 (List.mem_map.mpr ⟨source, inRest, equal.symm⟩)
      simp [different, ih both.2 inRest]

/-- Apply Clean's complete-path result separately to each memory address.
    Initial address uniqueness and strict time growth are the only extra premises;
    the statement supplies no expected read or write values. -/
theorem keyed_paths {S K : Type} [Fintype S] [DecidableEq S] [DecidableEq K]
    (key : S → K) (rank : S → Nat) {initial terminal : List S} {steps : List (S × S)}
    (matched : (initial ++ steps.map Prod.snd).Perm (terminal ++ steps.map Prod.fst))
    (preserved : ∀ edge ∈ steps, key edge.1 = key edge.2)
    (unique : (initial.map key).Nodup)
    (increases : ∀ edge ∈ steps, rank edge.1 < rank edge.2) :
    ∀ source ∈ initial, ∃ sink ∈ terminal, key sink = key source ∧
      ∃ path : List S, path.head? = some source ∧ path.getLast? = some sink ∧
        (path.map rank).Nodup ∧ (path.zip path.tail).Perm
          (steps.filter fun edge => key edge.1 = key source) := by
  have keys := boundary_keys key matched preserved
  have terminalUnique := keys.nodup_iff.mp unique
  intro source sourceMember
  have sinkKey := keys.mem_iff.mp (List.mem_map.mpr ⟨source, sourceMember, rfl⟩)
  obtain ⟨sink, sinkMember, sameKey⟩ := List.mem_map.mp sinkKey
  have first := key_filter_singleton key unique sourceMember
  have last := key_filter_singleton key terminalUnique sinkMember
  let selected := steps.filter fun edge => key edge.1 = key source
  have filtered := matched.filter (fun state => key state = key source)
  have sameFilter : steps.filter (fun edge => key edge.2 = key source) = selected := by
    apply List.filter_congr
    intro edge member
    rw [preserved edge member]
  simp only [List.filter_append, List.filter_map, Function.comp_def] at filtered
  rw [first, ← sameKey, last, sameKey, sameFilter] at filtered
  have selectedIncreases : ∀ edge ∈ selected, rank edge.1 < rank edge.2 := by
    intro edge member
    exact increases edge (List.mem_of_mem_filter member)
  obtain ⟨path, head, lastState, _, counts⟩ := matched_path rank filtered selectedIncreases
  have permutation : (path.zip path.tail).Perm selected := List.perm_iff_count.mpr counts
  have ordered := rank_unique rank path (by
    intro edge member
    exact selectedIncreases edge (permutation.mem_iff.mp member))
  exact ⟨sink, sinkMember, sameKey, path, head, lastState, ordered, permutation⟩

/-- Only the tokens occurring in the finite trace need a finite type. This checked
    support restriction lets Clean's finite-state utility handle arbitrary tokens. -/
theorem keyed_paths_finite {S K : Type} [DecidableEq S] [DecidableEq K]
    (key : S → K) (rank : S → Nat) {initial terminal : List S} {steps : List (S × S)}
    (matched : (initial ++ steps.map Prod.snd).Perm (terminal ++ steps.map Prod.fst))
    (preserved : ∀ edge ∈ steps, key edge.1 = key edge.2)
    (unique : (initial.map key).Nodup)
    (increases : ∀ edge ∈ steps, rank edge.1 < rank edge.2) :
    ∀ source ∈ initial, ∃ sink ∈ terminal, key sink = key source ∧
      ∃ path : List S, path.head? = some source ∧ path.getLast? = some sink ∧
        (path.map rank).Nodup ∧ (path.zip path.tail).Perm
          (steps.filter fun edge => key edge.1 = key source) := by
  let support := (initial ++ terminal ++ steps.flatMap (fun edge => [edge.1, edge.2])).toFinset
  let Node := {state : S // state ∈ support}
  letI : Fintype Node := inferInstance
  have initialSupport : ∀ state ∈ initial, state ∈ support := by
    intro state member
    simp only [support, List.mem_toFinset, List.mem_append]
    exact Or.inl (Or.inl member)
  have terminalSupport : ∀ state ∈ terminal, state ∈ support := by
    intro state member
    simp only [support, List.mem_toFinset, List.mem_append]
    exact Or.inl (Or.inr member)
  have stepSupport : ∀ edge ∈ steps, edge.1 ∈ support ∧ edge.2 ∈ support := by
    intro edge member
    constructor <;> simp only [support, List.mem_toFinset, List.mem_append]
    · exact Or.inr (List.mem_flatMap.mpr ⟨edge, member, by simp⟩)
    · exact Or.inr (List.mem_flatMap.mpr ⟨edge, member, by simp⟩)
  let starts : List Node := initial.attachWith (· ∈ support) initialSupport
  let ends : List Node := terminal.attachWith (· ∈ support) terminalSupport
  let transfers : List (Node × Node) := steps.attach.map fun edge =>
    (⟨edge.val.1, (stepSupport edge.val edge.property).1⟩,
      ⟨edge.val.2, (stepSupport edge.val edge.property).2⟩)
  have transferValues : transfers.map (fun edge => (edge.1.val, edge.2.val)) = steps := by
    simp only [transfers, List.map_map, Function.comp_def]
    exact List.attach_map_subtype_val steps
  have startValues : starts.map Subtype.val = initial := List.attachWith_map_subtype_val initialSupport
  have endValues : ends.map Subtype.val = terminal := List.attachWith_map_subtype_val terminalSupport
  have transferFirst : (transfers.map Prod.fst).map Subtype.val = steps.map Prod.fst := by
    have projected := congrArg (List.map Prod.fst) transferValues
    simpa only [List.map_map, Function.comp_def] using projected
  have transferLast : (transfers.map Prod.snd).map Subtype.val = steps.map Prod.snd := by
    have projected := congrArg (List.map Prod.snd) transferValues
    simpa only [List.map_map, Function.comp_def] using projected
  have lifted : (starts ++ transfers.map Prod.snd).Perm (ends ++ transfers.map Prod.fst) := by
    apply (List.map_perm_map_iff Subtype.val_injective).mp
    rw [List.map_append, List.map_append, startValues, endValues, transferFirst, transferLast]
    exact matched
  have liftedPreserved : ∀ edge ∈ transfers, key edge.1.val = key edge.2.val := by
    intro edge member
    have rawMember : (edge.1.val, edge.2.val) ∈
        transfers.map (fun item => (item.1.val, item.2.val)) :=
      List.mem_map.mpr ⟨edge, member, rfl⟩
    rw [transferValues] at rawMember
    exact preserved _ rawMember
  have liftedUnique : (starts.map fun state => key state.val).Nodup := by
    have projected := congrArg (List.map key) startValues
    simp only [List.map_map, Function.comp_def] at projected
    rw [projected]
    exact unique
  have liftedIncreases : ∀ edge ∈ transfers, rank edge.1.val < rank edge.2.val := by
    intro edge member
    have rawMember : (edge.1.val, edge.2.val) ∈
        transfers.map (fun item => (item.1.val, item.2.val)) :=
      List.mem_map.mpr ⟨edge, member, rfl⟩
    rw [transferValues] at rawMember
    exact increases _ rawMember
  intro source member
  let start : Node := ⟨source, initialSupport source member⟩
  have startMember : start ∈ starts := by
    exact (List.mem_attachWith initialSupport start).mpr member
  obtain ⟨sink, sinkMember, sameKey, path, head, last, ordered, permutation⟩ :=
    keyed_paths (fun state : Node => key state.val) (fun state => rank state.val)
      lifted liftedPreserved liftedUnique liftedIncreases start startMember
  refine ⟨sink.val, ?_, sameKey, path.map Subtype.val, ?_, ?_, ?_, ?_⟩
  · rw [← endValues]
    exact List.mem_map.mpr ⟨sink, sinkMember, rfl⟩
  · rw [List.head?_map, head]
    rfl
  · rw [List.getLast?_map, last]
    rfl
  · simpa only [List.map_map, Function.comp_def] using ordered
  · have mapped := permutation.map (fun edge => (edge.1.val, edge.2.val))
    rw [← List.map_tail, List.zip_map]
    have selected :
        (transfers.filter fun edge => key edge.1.val = key source).map
          (fun edge => (edge.1.val, edge.2.val)) =
        steps.filter (fun edge => key edge.1 = key source) := by
      calc
        _ = (transfers.map (fun edge => (edge.1.val, edge.2.val))).filter
            (fun edge => key edge.1 = key source) := List.filter_map.symm
        _ = _ := by rw [transferValues]
    rw [selected] at mapped
    exact mapped

theorem keyed_origins {S K : Type} [DecidableEq S] [DecidableEq K]
    (key : S → K) (rank : S → Nat) {initial terminal : List S} {steps : List (S × S)}
    (matched : (initial ++ steps.map Prod.snd).Perm (terminal ++ steps.map Prod.fst))
    (preserved : ∀ edge ∈ steps, key edge.1 = key edge.2)
    (increases : ∀ edge ∈ steps, rank edge.1 < rank edge.2) :
    ∀ edge ∈ steps, key edge.1 ∈ initial.map key := by
  have rooted : ∀ time : Nat, ∀ edge ∈ steps, rank edge.2 = time →
      key edge.1 ∈ initial.map key := by
    intro time
    induction time using Nat.strong_induction_on with
    | h time ih =>
      intro edge member clock
      have read := matched.mem_iff.mpr
        (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨edge, member, rfl⟩)))
      rcases List.mem_append.mp read with seed | written
      · exact List.mem_map.mpr ⟨edge.1, seed, rfl⟩
      · obtain ⟨writer, present, same⟩ := List.mem_map.mp written
        have earlier : rank writer.2 < time := by rw [same, ← clock]; exact increases edge member
        have source := ih _ earlier writer present rfl
        rwa [preserved writer present, same] at source
  intro edge member
  exact rooted _ edge member rfl

/-- Native matching expressed once over the imported transfer pairs. -/
theorem memory_steps_matched [Fact p.Prime] {trace : Data p Kind} (accepted : Accepted trace) :
    (trace.initialMemory ++ trace.memorySteps.map Prod.snd).Perm
      (trace.terminalMemory ++ trace.memorySteps.map Prod.fst) := by
  have reads : trace.memorySteps.map Prod.fst = trace.rows.flatMap Row.reads := by
    simp only [Data.memorySteps, Row.memorySteps, List.map_flatMap, List.map_map,
      Function.comp_def]
    rfl
  have writes : trace.memorySteps.map Prod.snd = trace.rows.flatMap Row.writes := by
    simp only [Data.memorySteps, Row.memorySteps, List.map_flatMap, List.map_map,
      Function.comp_def]
    rfl
  rw [reads, writes]
  exact accepted.memory

/-- Imported transfers retain their injectively encoded address. -/
theorem memory_steps_address [Fact p.Prime] {trace : Data p Kind} :
    ∀ edge ∈ trace.memorySteps, edge.1.address = edge.2.address := by
  intro edge member
  change edge ∈ trace.rows.flatMap Row.memorySteps at member
  obtain ⟨row, _, stepMember⟩ := List.mem_flatMap.mp member
  dsimp only [Row.memorySteps] at stepMember
  obtain ⟨port, _, rfl⟩ := List.mem_map.mp stepMember
  rfl

/-- Every imported transfer advances its actual native access clock. -/
theorem memory_steps_increase [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p timestampBase)
    [ClockLaws Kind p] (inverse : SerializedInverse.Clock p) {trace : Data p Kind}
    (accepted : Accepted trace) (boundary : ClockBoundary trace) :
    ∀ edge ∈ trace.memorySteps,
      (timeOfPair edge.1.time).value < (timeOfPair edge.2.time).value := by
  intro edge member
  change edge ∈ trace.rows.flatMap Row.memorySteps at member
  obtain ⟨row, rowMember, stepMember⟩ := List.mem_flatMap.mp member
  dsimp only [Row.memorySteps] at stepMember
  obtain ⟨port, portListMember, rfl⟩ := List.mem_map.mp stepMember
  have arrayMember : port ∈ row.ports := by simpa using portListMember
  have clockMember : port.clock ∈ row.columns.ports := by
    rw [← ports_clocks row]
    exact Array.mem_map.mpr ⟨port, arrayMember, rfl⟩
  have inputs := clock_inputs hp inverse accepted boundary row rowMember
  have order := (trace_clocks hp inverse accepted boundary row rowMember).accesses
    port.clock clockMember
  have written := (write_time (by omega)
    (base := rawPair row.assignment row.columns.initialTime)
    inputs.initial inputs.aligned (port_offset row port arrayMember)).2
  exact order.1.trans_eq written.symm

/-- Complete per-address histories for the actual imported ports. The additional
    boundary premise states that the initial image has one cell per address. -/
theorem native_memory_paths [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p timestampBase)
    [ClockLaws Kind p] (inverse : SerializedInverse.Clock p) {trace : Data p Kind}
    (accepted : Accepted trace) (boundary : ClockBoundary trace)
    (unique : (trace.initialMemory.map MemoryToken.address).Nodup) :
    ∀ source ∈ trace.initialMemory, ∃ path, MemoryPath trace source path := by
  have matched := memory_steps_matched accepted
  have preserved := memory_steps_address (trace := trace)
  have increases := memory_steps_increase hp inverse accepted boundary
  intro source member
  obtain ⟨sink, sinkMember, sameKey, path, head, last, _, permutation⟩ :=
    keyed_paths_finite MemoryToken.address (fun token => (timeOfPair token.time).value)
      matched preserved unique increases source member
  have ordered := rank_ordered (fun token : MemoryToken p => (timeOfPair token.time).value) path (by
    intro edge edgeMember
    exact increases edge (List.mem_of_mem_filter (permutation.mem_iff.mp edgeMember)))
  exact ⟨path, head, ⟨sink, sinkMember, last, sameKey⟩, ordered, permutation⟩

end Airbender.Trace.Proofs
