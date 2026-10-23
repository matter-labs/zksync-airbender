import Airbender.Review.Trace.UnifiedReduced.Paths.Calls
import Airbender.Proofs.UnifiedReduced.PathControllerDataflow
import Airbender.Proofs.UnifiedReduced.PathGPointerSeed
import Airbender.Proofs.Blake2Round.ExclusiveMask

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Trace.Proofs Arithmetic Reference.RiscV.Sail Reference.Sail
set_option warningAsError true

/-- Every actual worker, in all four families, has a public occurrence plan.
    The fixed clock coefficient selects BabyBear; current imported timestamp
    constraints derive participation before any controller mask or history.
    No external ledger or all-issued premise is introduced. -/
theorem path_worker_call_plan [Fact p.Prime]
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {plans : List (PathCallPlan data program)}
    (accepted : RequestChecks data) (inputs : PathCallsInputs data before ca oa cells program plans)
    {worker : Delegation.Row p} (member : worker ∈ data.workers.rows) :
    ∃ plan ∈ plans, plan.Matches worker := by
  have characteristic := SerializedInverse.clock_field inverse
  subst p
  have requests := request_binding (by decide) inverse accepted inputs.publicProgram
  have native := ExternalBoundary.Requests.Proofs.native_binding accepted requests
  obtain ⟨caller, called, matched, slot⟩ := ExternalBoundary.Requests.Proofs.covered requests native worker member
  have decoded := accepted.decoded caller called
  change ∃ i : Fin data.program.length, caller.decoderQuery = Delegation.Caller.query (data.program.get i) at decoded
  obtain ⟨i, query⟩ := decoded
  let entry := data.program.get i
  have present : entry ∈ data.program := List.get_mem _ _
  have pcWord : caller.start.word = Word.ofBitVec entry.pc := caller_query_pc_word (by decide) query
  have pc : entry.pc = caller.start.word.toBitVec := by rw [pcWord, Word.ofBitVec_roundtrip]
  obtain ⟨plan, included, start, family⟩ := inputs.coverage caller (List.mem_of_mem_filter called) entry present pc
  have actual := caller_worker_family (by decide) query matched
  exact ⟨plan, included, family.trans actual.symm, caller, called, start, matched, slot⟩

/-- Distinct public cuts and native slots give one plan per worker occurrence.
    Equal PCs at different cuts are never identified. -/
theorem path_worker_call_plan_unique [Fact p.Prime]
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {plans : List (PathCallPlan data program)}
    (accepted : RequestChecks data) (inputs : PathCallsInputs data before ca oa cells program plans)
    {worker : Delegation.Row p} (member : worker ∈ data.workers.rows) :
    ∃! plan, plan ∈ plans ∧ plan.Matches worker := by
  obtain ⟨plan, present, matched⟩ := path_worker_call_plan inverse accepted inputs member
  refine ⟨plan, ⟨present, matched⟩, ?_⟩
  intro other checked
  obtain ⟨_, caller, called, start, _, slot⟩ := matched
  obtain ⟨_, otherCaller, otherCalled, otherStart, _, otherSlot⟩ := checked.2
  have same : other.start = plan.start := by
    have first := slot.invocation
    have second := otherSlot.invocation
    rw [start, otherStart]
    omega
  exact List.inj_on_of_nodup_map inputs.distinctPlans checked.1 present same

/-- The matched native slot places this worker in its actual public caller
    occurrence. Equal PCs do not merge slots or clocks. -/
theorem path_plan_worker_window [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p timestampBase)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca : List (BitVec 32)} {plan : PathCallPlan data program} {worker : Delegation.Row p}
    (accepted : RequestChecks data) (publicProgram : RequestInputs data before ca)
    (member : worker ∈ data.workers.rows) (matched : plan.Matches worker) :
    plan.start % 4 = 0 ∧ worker ∈ data.workers.windowRows plan.start (plan.start + 4) := by
  obtain ⟨_, caller, called, start, _, slot⟩ := matched
  have clock := machine_clock_facts hp inverse accepted publicProgram (List.mem_of_mem_filter called)
  have write := slot.writes (path_native_control_port worker.family) (path_control_port_member worker)
  have normalized : worker.writeTime =
      (timeOfPair (worker.writeToken (path_native_control_port worker.family)).time).value := by
    cases worker with
    | mk family w => cases family <;> rfl
  refine ⟨by simpa only [start] using clock.1, List.mem_filter.mpr ⟨member, decide_eq_true ?_⟩⟩
  rw [normalized, write, ← start]
  omega

/-- Syntactic preparation plus raw matching derives the actual control read at
    every hash call, including every nonzero controller position. -/
theorem path_plan_hash_binding [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {plans : List (PathCallPlan data program)}
    (accepted : MixedMemoryAccepted data program) (inputs : PathCallsInputs data before ca oa cells program plans)
    {plan : PathCallPlan data program} {worker : Delegation.Row p} (position : HashCallPosition)
    (form : plan.position = .hash position) (member : worker ∈ data.workers.rows)
    (matched : plan.Matches worker) : position.NativeBinding worker := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  obtain ⟨aligned, inside⟩ := path_plan_worker_window size inverse accepted.toRequestChecks
    inputs.publicProgram member matched
  have scope : PathCallerPreparation data (plan.start + 4) position.span.family := by
    simpa only [form, PathCallPosition.family] using plan.code
  have flow : PathControllerDataflow data program plan.start position.span.controlRegister position.word.toBitVec := by
    simpa only [form, PathCallPosition.Preparation] using plan.preparation
  have unique : (data.machine.initialMemory.map MemoryToken.address).Nodup := by
    rw [image_addresses inputs.initialization]
    exact inputs.distinct
  have nonzero : position.span.controlRegister ≠ 0 := by
    cases position with
    | mk span index =>
      cases span with
      | blakeG reduced => change (12 : BitVec 5) ≠ 0; decide
      | blakeRound flags => change (12 : BitVec 5) ≠ 0; decide
      | keccak => change (10 : BitVec 5) ≠ 0; decide
  have family : worker.family = position.span.family := by
    have actual := matched.1
    simpa only [form, PathCallPosition.family] using actual.symm
  have raw := path_caller_control_read hp inverse accepted inputs.publicProgram inputs.ordinaryProgram
    inputs.initialization unique scope (by omega : (plan.start + 4) % 4 = 0)
    (value := position.word.toBitVec)
    (by
      intro start prefixMatching
      have seed := path_controller_dataflow_token hp inverse accepted inputs.publicProgram
        inputs.ordinaryProgram inputs.initialization unique inputs.tables flow nonzero aligned
        (by simpa using prefixMatching)
      simpa only [path_hash_control_register] using seed)
    (by simpa using inside)
  have read := raw.trans (path_hash_word_canonical position)
  refine ⟨family, ?_⟩
  cases position with
  | mk span index =>
    cases span <;> simpa only [family, path_native_control_port, Delegation.Caller.HashSpan.family] using read

/-- Every actual hash worker has the derived exact controller binding. Native
    complete participation supplies the plan, rather than an issued ledger. -/
theorem path_calls_hash_bindings [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {plans : List (PathCallPlan data program)}
    (accepted : MixedMemoryAccepted data program) (inputs : PathCallsInputs data before ca oa cells program plans)
    {worker : Delegation.Row p} (member : worker ∈ data.workers.rows) (hash : worker.family ≠ .bigint) :
    ∃ position : HashCallPosition, position.NativeBinding worker := by
  obtain ⟨plan, _, matched⟩ := path_worker_call_plan inverse accepted.toRequestChecks inputs member
  cases form : plan.position with
  | bigint =>
    have family := matched.1
    simp only [form, PathCallPosition.family] at family
    exact False.elim (hash family.symm)
  | hash position =>
    exact ⟨position, path_plan_hash_binding hp inverse accepted inputs position form member matched⟩

private theorem path_round_power_bound (round : Fin 10) : 2 ^ round.val < 1024 := by
  fin_cases round <;> decide

/-- The actual imported control equations derive each extended-round mask
    from public position and raw reads. No mask enters the path contract. -/
theorem path_calls_round_mask [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {plans : List (PathCallPlan data program)}
    (accepted : MixedMemoryAccepted data program) (inputs : PathCallsInputs data before ca oa cells program plans)
    {worker : Delegation.Row p} (member : worker ∈ data.workers.rows) (family : worker.family = .blakeRound) :
    ∃ round, Blake2Round.Memory.RoundMask worker.assignment round := by
  have hash : worker.family ≠ .bigint := by rw [family]; decide
  obtain ⟨position, binding⟩ := path_calls_hash_bindings hp inverse accepted inputs member hash
  cases position with
  | mk span index =>
    cases span with
    | blakeG reduced =>
      have same := binding.1
      rw [family] at same
      cases same
    | keccak =>
      have same := binding.1
      rw [family] at same
      cases same
    | blakeRound flags =>
      have indexBound : index.val < 10 := by
        have bound := index.isLt
        dsimp only [Delegation.Caller.HashSpan.callCount] at bound
        split_ifs at bound <;> omega
      let round : Fin 10 := ⟨index.val, indexBound⟩
      have power : 2 ^ index.val < 1024 := path_round_power_bound round
      cases worker with
      | mk nativeFamily w =>
        change nativeFamily = .blakeRound at family
        subst nativeFamily
        have holds := accepted.workerConstraints (⟨.blakeRound, w⟩ : Delegation.Row p) member
        change FlatOperation.ConstraintsHoldFlat (Verification.environment w)
          (Blake2Round.clockConstraints data.workers.setup.blakeRound) at holds
        have core : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
            (Blake2Round.importedConstraints data.workers.setup.blakeRound) :=
          Verification.holds_of_sublist holds (List.sublist_append_left _ _)
        have read : (w Blake2Round.Variables.controlReadHi).val = flags.val + 8 * 2 ^ round.val := by
          have high := congrArg Word.hi binding.2
          simpa [HashCallPosition.word, Blake2Round.controlAt,
            readToken, MemoryToken.word, MemoryPort.readCode, Blake2Round.importedConstraintsMemoryPorts,
            WordColumns.code, WordColumns.evaluate, Nat.mod_eq_of_lt power] using high
        exact ⟨round, Blake2Round.Proofs.exclusive_mask (by omega) core flags round read⟩

/-- The round-mask field required by the existing mixed memory theorem is now
    derived for the complete native pool; all other fields are public context. -/
theorem path_calls_memory_inputs [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {plans : List (PathCallPlan data program)}
    (accepted : MixedMemoryAccepted data program) (inputs : PathCallsInputs data before ca oa cells program plans) :
    MixedMemoryInputs data program before ca oa cells := by
  exact ⟨inputs.publicProgram, inputs.ordinaryProgram, inputs.initialization, inputs.distinct,
    inputs.aligned, inputs.setup, inputs.tables,
    fun worker member family => path_calls_round_mask hp inverse accepted inputs member family⟩

/-- Public GPR dataflow fixes every native read-refresh port in an actual
    caller window. This also supplies pointer words independently of the
    controller transfer; no pointer value is read from an assumed ABI. -/
theorem path_caller_frame_read [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {cut : Nat} {family : Delegation.Family}
    {value : BitVec 32} {register : BitVec 5}
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (image : initialImage before cells = some data.machine.initialMemory)
    (uniqueSeeds : (data.machine.initialMemory.map MemoryToken.address).Nodup)
    (scope : PathCallerPreparation data cut family) (aligned : cut % 4 = 0)
    (nonzero : register ≠ 0) (different : register ≠ callerControlRegister family)
    (seedToken : ∀ start : List (MemoryToken p),
      (data.machine.initialMemory ++ (data.prefixSteps (cut - 4)).map Prod.snd).Perm
        (start ++ (data.prefixSteps (cut - 4)).map Prod.fst) →
      ∃ token ∈ start, token.address = (Cell.register register).addressCode ∧ token.word = Word.ofBitVec value)
    {worker : Delegation.Row p} (member : worker ∈ data.workers.windowRows (cut - 4) cut)
    {port : MemoryPort} (portMember : port ∈ worker.ports)
    (portAddress : port.address.code worker.assignment = (Cell.register register).addressCode) :
    (readToken worker.assignment port).word = Word.ofBitVec value := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  obtain ⟨floor, _⟩ := path_caller_window hp inverse accepted publicProgram ordinaryProgram image scope aligned
  have first : (cut - 4) % 4 = 0 := by omega
  have requests := request_binding size inverse accepted.toRequestChecks publicProgram
  have facts := mixed_memory_facts size inverse accepted publicProgram image requests
  obtain ⟨start, earlier, later⟩ := Transfer.split_at facts ((cut - 4) - 1)
  have prefixMatching := earlier.matching
  rw [mixed_prefix_steps data (by omega)] at prefixMatching
  obtain ⟨source, sourceMember, sourceAddress, sourceWord⟩ := seedToken start prefixMatching
  obtain ⟨finish, window, _⟩ := Transfer.split_at later (cut - 1)
  change Transfer.Facts ⟨start, finish, Transfer.windowSteps (mixedData data) ((cut - 4) - 1) (cut - 1)⟩ at window
  rw [← mixed_window_steps size inverse accepted.toRequestChecks publicProgram first aligned (by omega) (by omega)] at window
  have keys := boundary_keys MemoryToken.address earlier.matching earlier.addresses
  have unique : (start.map MemoryToken.address).Nodup := keys.nodup_iff.mp uniqueSeeds
  have seed : ∀ token ∈ start, token.address = (Cell.register register).addressCode → token.value = source.value := by
    intro token present address
    exact congrArg MemoryToken.value (List.inj_on_of_nodup_map unique present sourceMember
      (address.trans sourceAddress.symm))
  have refreshes := path_caller_frame_refreshes hp inverse accepted publicProgram ordinaryProgram
    image scope nonzero different aligned
  have values := Transfer.read_cell_values window (Cell.register register).addressCode source.value seed
    (by intro edge present address read; exact (refreshes edge present address).trans read)
  have included : (readToken worker.assignment port, worker.writeToken port) ∈ data.windowSteps (cut - 4) cut :=
    List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
      ⟨worker, member, List.mem_map.mpr ⟨port, by simpa using portMember, rfl⟩⟩))
  have raw := values _ included portAddress
  change (readToken worker.assignment port).value = source.value at raw
  have same : (readToken worker.assignment port).word = source.word :=
    congrArg (fun value : Nat => (⟨(Nat.unpair value).1, (Nat.unpair value).2⟩ : Word)) raw
  exact same.trans sourceWord

/-- Public computed or seeded bases derive the actual native G ABI separation. Every
    controller index is admitted; no native inequality or desired read appears
    in the input contract. -/
theorem path_plan_g_pointer_binding [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {plans : List (PathCallPlan data program)}
    (accepted : MixedMemoryAccepted data program) (inputs : PathCallsInputs data before ca oa cells program plans)
    {plan : PathCallPlan data program} {worker : Delegation.Row p} {reduced : Bool}
    {index : Fin (Delegation.Caller.HashSpan.blakeG reduced).callCount}
    (form : plan.position = .hash ⟨.blakeG reduced, index⟩)
    (member : worker ∈ data.workers.rows) (matched : plan.Matches worker) :
    (Blake2G.Native.statePointer worker.assignment).toBitVec ≠
      (Blake2G.Native.messagePointer worker.assignment).toBitVec := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  obtain ⟨aligned, inside⟩ := path_plan_worker_window size inverse accepted.toRequestChecks
    inputs.publicProgram member matched
  have scope : PathCallerPreparation data (plan.start + 4) .blakeG := by
    simpa only [form, PathCallPosition.family, Delegation.Caller.HashSpan.family] using plan.code
  have publicPointers : PathGPointerPreparation data program plan.start := by
    simpa only [form, PathCallPosition.PointerPreparation] using plan.pointers
  rcases publicPointers with computed | seed
  · obtain ⟨stateValue, messageValue, different, stateFlow, messageFlow⟩ := computed
    have unique : (data.machine.initialMemory.map MemoryToken.address).Nodup := by
      rw [image_addresses inputs.initialization]
      exact inputs.distinct
    have family : worker.family = .blakeG := by
      have actual := matched.1
      simpa only [form, PathCallPosition.family, Delegation.Caller.HashSpan.family] using actual.symm
    have pointers (register : BitVec 5) (value : BitVec 32)
        (flow : PathControllerDataflow data program plan.start register value)
        (nonzero : register ≠ 0) (notControl : register ≠ 12)
        (port : MemoryPort) (portMember : port ∈ worker.ports)
        (address : port.address.code worker.assignment = (Cell.register register).addressCode) :
        (readToken worker.assignment port).word = Word.ofBitVec value := by
      apply path_caller_frame_read hp inverse accepted inputs.publicProgram inputs.ordinaryProgram
        inputs.initialization unique scope (by omega : (plan.start + 4) % 4 = 0)
        nonzero notControl _ (by simpa using inside) portMember address
      intro start prefixMatching
      exact path_controller_dataflow_token hp inverse accepted inputs.publicProgram inputs.ordinaryProgram
        inputs.initialization unique inputs.tables flow nonzero aligned (by simpa using prefixMatching)
    cases worker with
    | mk nativeFamily w =>
      change nativeFamily = .blakeG at family
      subst nativeFamily
      have state := pointers 10 stateValue stateFlow (by decide) (by decide)
        Blake2G.importedConstraintsMemoryPorts[0] (by exact Array.getElem_mem (by change 0 < 9; decide)) rfl
      have message := pointers 11 messageValue messageFlow (by decide) (by decide)
        Blake2G.importedConstraintsMemoryPorts[5] (by exact Array.getElem_mem (by change 5 < 9; decide)) rfl
      change Blake2G.Native.statePointer w = Word.ofBitVec stateValue at state
      change Blake2G.Native.messagePointer w = Word.ofBitVec messageValue at message
      rw [state, message, Word.ofBitVec_roundtrip, Word.ofBitVec_roundtrip]
      exact different
  · have characteristic := SerializedInverse.clock_field inverse
    subst p
    exact path_g_pointer_seed_binding accepted
      (path_calls_memory_inputs (by decide) inverse accepted inputs) seed scope aligned inside

end Airbender.UnifiedReduced.Caller.Proofs
