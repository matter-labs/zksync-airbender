import Airbender.Review.Circuits.ReducedMachine.MainStateHistory
import Airbender.Proofs.ReducedMachine.NativeTokenLedger
import Airbender.Proofs.Trace.Families.ReducedMachine.History
import Airbender.Proofs.Trace.Slots

namespace Airbender.NativeMainStateHistoryProofs
open NativeMainStateHistory NativeTokenLedger Trace Airbender.ReducedMachine.NativeMainAuxiliary
open Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

private theorem memory_states (tokens : List (MemoryToken mersenne31Modulus)) :
    ((tokens.map Token.memory).filterMap stateProjection) = [] := by
  simp [List.filterMap_map,stateProjection]

theorem port_states (w : Nat → F) (write : Bool) :
    (portTokens w write).filterMap stateProjection = [mainPCKey w write] := by
  rw [portTokens,List.filterMap_append,memory_states]
  rfl

theorem row_states (w : Nat → F) (write : Bool) :
    (activeRowTokens w write).filterMap stateProjection =
      if w Airbender.ReducedMachine.Native.importedConstraintsTraceColumns.execute = 1 then [mainPCKey w write] else [] := by
  change (if w Airbender.ReducedMachine.Native.importedConstraintsTraceColumns.execute = 1
    then portTokens w write else []).filterMap stateProjection = _
  split <;> simp only [port_states,List.filterMap_nil]

theorem ordinary_states (assignments : List (Nat → F)) (write : Bool) :
    (assignments.flatMap fun w => activeRowTokens w write).filterMap stateProjection =
      (selectAssignments assignments).map fun w => mainPCKey w write := by
  induction assignments with
  | nil => rfl
  | cons w assignments ih =>
    rw [List.flatMap_cons,List.filterMap_append,row_states,ih]
    by_cases active : w Airbender.ReducedMachine.Native.importedConstraintsTraceColumns.execute = 1
    all_goals simp [selectAssignments,active]

theorem worker_states (assignments : List (Nat → F)) (write : Bool) :
    (assignments.flatMap fun w => workerRowTokens w write).filterMap stateProjection = [] := by
  induction assignments with
  | nil => rfl
  | cons w assignments ih =>
    rw [List.flatMap_cons,List.filterMap_append,ih]
    change ((Airbender.NativeMemoryTokens.workerTokens w write).map Token.memory).filterMap stateProjection ++ [] = []
    rw [memory_states]
    rfl

theorem public_states (inputs : PublicBoundary) (write : Bool) :
    (publicTokens inputs write).filterMap stateProjection = [if write then initialPCKey else finalPCKey inputs] := by
  have memory := memory_states ((List.finRange 32).map fun index => Airbender.NativeMemoryTokens.encodeKey
    (if write then registerInitialKey index else registerFinalKey inputs index))
  simpa only [publicTokens,List.filterMap_append,List.map_map,Function.comp_def,List.filterMap_cons,
    stateProjection,List.filterMap_nil,List.nil_append] using congrArg (fun tokens => tokens++
      [if write then initialPCKey else finalPCKey inputs]) memory

theorem active_states {Setup R : Type} [Field R] (mains : List (MainProof R))
    (batch : WorkerBatch Setup R) (inputs : PublicBoundary) (write : Bool) :
    (activeTokens mains batch inputs write).filterMap stateProjection =
      (if write then initialPCKey else finalPCKey inputs) ::
        (selectAssignments (mainRows mains)).map (fun w => mainPCKey w write) := by
  simp only [activeTokens,List.filterMap_append,public_states,ordinary_states,worker_states,
    List.append_nil,List.singleton_append]

theorem row_state (w : Nat → F) (write : Bool) :
    state (mainPCKey w write) =
      if write then (⟨.reduced,w⟩ : Row mersenne31Modulus NativeReducedFamily).finish
      else (⟨.reduced,w⟩ : Row mersenne31Modulus NativeReducedFamily).start := by
  have columns : CircuitLayout.columns NativeReducedFamily.reduced =
      Airbender.ReducedMachine.Native.importedConstraintsTraceColumns := rfl
  cases write <;> simp [state,mainPCKey,Row.start,Row.finish,rawPair,Row.columns,columns]

theorem state_matching {Setup R : Type} [Field R] {mains : List (MainProof R)}
    {batch : WorkerBatch Setup R} {inputs : PublicBoundary} (matching : LogicalMatching mains batch inputs) :
    (state initialPCKey :: (rows mains).map Row.finish).Perm
      (state (finalPCKey inputs) :: (rows mains).map Row.start) := by
  have projected := (NativeTokenLedgerProofs.projected_matching matching).2
  rw [active_states,active_states] at projected
  have native := projected.map state
  simpa [rows,List.map_map,Function.comp_def,row_state] using native

private theorem sample_property {A B : Type} (objects : List A) (samples : A → Nat → B)
    (count : Nat) (property : B → Prop)
    (checked : ∀ object ∈ objects, ∀ i < count, property (samples object i)) :
    ∀ sample ∈ objects.flatMap (fun object => (List.range count).map (samples object)), property sample := by
  intro sample member
  obtain ⟨object,present,sampled⟩ := List.mem_flatMap.mp member
  obtain ⟨i,bound,rfl⟩ := List.mem_map.mp sampled
  exact checked object present i (List.mem_range.mp bound)

theorem selected_body {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (mains : List (MainProof R))
    (accepted : ∀ proof ∈ mains, Airbender.ReducedMachine.NativeMainAuxiliary.Accepted embed memory pc proof) :
    ∀ row ∈ rows mains, FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints Airbender.ReducedMachine.NativeRuntimePool.table) := by
  have checked : ∀ proof ∈ mains, ∀ i < Airbender.ReducedMachine.Native.callerAuxiliaryLayout.traceLength-1,
      FlatOperation.ConstraintsHoldFlat (Verification.environment (proof.rows i))
        (Airbender.ReducedMachine.Native.importedConstraints Airbender.ReducedMachine.NativeRuntimePool.table) := by
    intro proof member i bound
    exact ((accepted proof member).rows i bound).body
  have ordinary := sample_property mains MainProof.rows
    (Airbender.ReducedMachine.Native.callerAuxiliaryLayout.traceLength-1)
    (fun w => FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Airbender.ReducedMachine.Native.importedConstraints Airbender.ReducedMachine.NativeRuntimePool.table)) checked
  intro row member
  obtain ⟨w,present,rfl⟩ := List.mem_map.mp member
  exact ordinary w (List.mem_filter.mp present).1

theorem initial_clock : timeOfPair (state initialPCKey).timestamp = ⟨4,0⟩ := by decide +kernel

private def observationTrace {R : Type} [Field R] (mains : List (MainProof R))
    (inputs : PublicBoundary) : Data mersenne31Modulus NativeReducedFamily :=
  ⟨rows mains,Airbender.ReducedMachine.NativeRuntimePool.table,state initialPCKey,
    state (finalPCKey inputs),[],[]⟩

private theorem write_times_unique (selected : List (Row mersenne31Modulus NativeReducedFamily))
    (unique : (selected.map Row.clock).Nodup)
    (aligned : ∀ row ∈ selected, (decodeTimestamp row.assignment row.columns.initialTime).lo % 4 = 0) :
    (selected.flatMap fun row => row.ports.toList.map fun port => row.clock+port.clock.offset).Nodup := by
  have alignment : ∀ time ∈ selected.map Row.clock, time % 4 = 0 := by
    intro time member
    obtain ⟨row,present,rfl⟩ := List.mem_map.mp member
    simpa [Row.clock,decodeTimestamp,Timestamp.value,Nat.add_mod,Nat.mul_mod,timestampBase] using aligned row present
  have result := Trace.Proofs.slots_unique unique alignment
  change ((selected.map Row.clock).flatMap fun time => [time,time+1,time+2]).Nodup at result
  have actual : (selected.flatMap fun row => row.ports.toList.map fun port => row.clock+port.clock.offset) =
      (selected.map Row.clock).flatMap (fun time => [time,time+1,time+2]) := by
    rw [List.flatMap_map]
    apply congrArg (fun f : Row mersenne31Modulus NativeReducedFamily → List Nat => selected.flatMap f)
    funext row
    have offsets : row.ports.toList.map (fun port => port.clock.offset) = [0,1,2] := by
      cases row with
      | mk family w =>
        cases family
        exact Airbender.ReducedMachine.NativeClockProofs.memory_offsets
    have mapped := congrArg (List.map (row.clock+·)) offsets
    simpa only [List.map_map,Function.comp_def,List.map_cons,List.map_nil,Nat.add_zero] using mapped
  rw [actual]
  exact result

/-- Private state-only reuse of existing graph/clock proofs. Empty memory fields
    are placeholders; no Accepted memory trace or Sail execution is constructed. -/
theorem history {Setup R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) {mains : List (MainProof R)}
    {batch : WorkerBatch Setup R} {inputs : PublicBoundary}
    (accepted : ∀ proof ∈ mains, Airbender.ReducedMachine.NativeMainAuxiliary.Accepted embed memory pc proof)
    (matching : LogicalMatching mains batch inputs) : Effects mains inputs := by
  let trace := observationTrace mains inputs
  have body := selected_body embed memory pc mains accepted
  have states := state_matching matching
  have initialTime : timeOfPair trace.initial.timestamp = ⟨4,0⟩ := initial_clock
  have initial : (timeOfPair trace.initial.timestamp).Bounded := by rw [initialTime]; constructor <;> decide +kernel
  have aligned : (timeOfPair trace.initial.timestamp).value % 4 = 0 := by rw [initialTime]; decide +kernel
  have initialValue : (timeOfPair trace.initial.timestamp).value = 4 := by rw [initialTime]; rfl
  have clocks := Trace.Proofs.state_clock_inputs (by decide) (trace := trace) body states initial aligned
  have finalClocks : ∀ row ∈ trace.rows, (decodeTimestamp row.assignment row.columns.finalTime).Bounded := by
    intro row member
    exact Trace.Proofs.ClockLaws.finalBound trace.rom row (body row member)
  have terminalBound : (timeOfPair trace.terminal.timestamp).Bounded := by
    have balanced : (trace.initial :: trace.rows.map Row.finish).Perm
        (trace.terminal :: trace.rows.map Row.start) := states
    have member := balanced.mem_iff.mpr (List.mem_cons_self)
    rcases List.mem_cons.mp member with same | outgoing
    · rw [same]
      exact initial
    · obtain ⟨row,present,same⟩ := List.mem_map.mp outgoing
      rw [← same]
      exact finalClocks row present
  have advances : ∀ row ∈ trace.rows,
      (decodeTimestamp row.assignment row.columns.finalTime).value =
        (decodeTimestamp row.assignment row.columns.initialTime).value+4 := by
    intro row member
    exact Trace.Proofs.ClockLaws.advance (by decide) trace.rom row (body row member) (clocks row member).1
  have clockMatch : (timeOfPair trace.initial.timestamp :: (Trace.Proofs.clockSteps trace).map Prod.snd).Perm
      (timeOfPair trace.terminal.timestamp :: (Trace.Proofs.clockSteps trace).map Prod.fst) := by
    simpa [trace,observationTrace,Trace.Proofs.clockSteps,List.map_map,Function.comp_def,Row.start,Row.finish,
      timeOfPair,rawPair,decodeTimestamp] using states.map (fun point => timeOfPair point.timestamp)
  have stepAdvance : ∀ step ∈ Trace.Proofs.clockSteps trace, step.2.value = step.1.value+4 := by
    intro step member
    obtain ⟨row,present,rfl⟩ := List.mem_map.mp member
    exact advances row present
  have terminal := Trace.Proofs.terminal_clock clockMatch stepAdvance
  have interval := Trace.Proofs.state_clock_interval (by decide) (trace := trace) body states initial aligned
  rw [initialValue] at terminal interval
  have unique := Trace.Proofs.state_clocks_unique (by decide) (trace := trace) body states initial aligned
  refine ⟨states,clocks,finalClocks,terminalBound,advances,interval,unique,?_,?_,?_,?_⟩
  · intro row present port portMember
    have result := Trace.Proofs.write_time (base := rawPair row.assignment row.columns.initialTime)
      (by decide : timestampBase < mersenne31Modulus)
      (clocks row present).1 (clocks row present).2 (Trace.Proofs.port_offset row port portMember)
    simpa only [writeToken,Row.clock,rawPair,timeOfPair,decodeTimestamp] using result
  · exact write_times_unique trace.rows unique (fun row member => (clocks row member).2)
  · simpa only [trace,observationTrace,Trace.Proofs.clockSteps,List.length_map] using terminal
  · exact Trace.Proofs.state_path_checks (by decide) (trace := trace) body states initial aligned

end Airbender.NativeMainStateHistoryProofs
