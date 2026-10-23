import Airbender.Review.Trace.UnifiedReduced.Paths.ControllerDataflow
import Airbender.Proofs.UnifiedReduced.PathDataflow
import Airbender.Proofs.UnifiedReduced.CallerCycles
import Airbender.Proofs.Blake2G.NativeCall
import Airbender.Proofs.Blake2Round.Control
import Airbender.Proofs.Keccak.NativeCall
import Airbender.Proofs.ExternalBoundary.Requests
import Airbender.Proofs.SerializedInverse

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Trace.Proofs Arithmetic Reference.RiscV.Sail Reference.Sail
set_option warningAsError true

/-- Original delegation CSR constructors have no ordinary metadata projection. -/
theorem path_caller_projection_disjoint {instruction : SailRV32.instruction}
    {fields : DecoderData Delegation.Family}
    (selected : Delegation.Caller.decoderFields instruction = some fields) :
    Mixed.decoderFields instruction = none := by
  unfold Delegation.Caller.decoderFields at selected
  split at selected
  all_goals first | rfl | cases selected

/-- Public CSR bytes at the actual occurrence force caller classification. -/
theorem path_caller_row_called [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p timestampBase)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cut : Nat} {family : Delegation.Family}
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (scope : PathCallerPreparation data cut family)
    {row : Trace.Row p UnifiedFamily} (member : row ∈ data.machine.rows)
    (last : Delegation.Caller.startClock row + 4 = cut) : row ∈ data.callers := by
  obtain ⟨called, present, calledPC, _⟩ := scope.code row member last
  have calledSource := run_program_sources publicProgram.image called present
  by_contra ordinary
  obtain ⟨entry, included, _, query⟩ := decoder_member (accepted.ordinaryDecoded row member ordinary)
  have actual : row.start.word = Word.ofBitVec entry.pc := by
    cases row with
    | mk kind w =>
      cases kind
      exact native_query_pc_word (by dsimp [limbBase]; norm_num [timestampBase] at hp; omega) query
  have pc : entry.pc = row.start.word.toBitVec := by rw [actual, Word.ofBitVec_roundtrip]
  have source := run_program_sources ordinaryProgram entry included
  have same := path_source_instruction_unique source calledSource (pc.trans calledPC.symm)
  have fields := source.fields
  rw [same, path_caller_projection_disjoint calledSource.fields] at fields
  cases fields

/-- The native query recovers the same public CSR family, with no native family
    selector or desired worker supplied by the occurrence scope. -/
theorem path_caller_entry [Fact p.Prime] (hp : FieldCapacity.ClockNoWrap p timestampBase)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cut : Nat} {family : Delegation.Family}
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (scope : PathCallerPreparation data cut family)
    {row : Trace.Row p UnifiedFamily} (member : row ∈ data.machine.rows)
    (last : Delegation.Caller.startClock row + 4 = cut) :
    row ∈ data.callers ∧ ∃ entry ∈ data.program,
      row.decoderQuery = Delegation.Caller.query entry ∧
      entry.pc = row.start.word.toBitVec ∧ entry.data.family = family := by
  have caller := path_caller_row_called hp accepted publicProgram ordinaryProgram scope member last
  have decoded := accepted.decoded row caller
  change ∃ i : Fin data.program.length, row.decoderQuery = Delegation.Caller.query (data.program.get i) at decoded
  obtain ⟨i, query⟩ := decoded
  let entry := data.program.get i
  have present : entry ∈ data.program := List.get_mem _ _
  have source := run_program_sources publicProgram.image entry present
  have actual : row.start.word = Word.ofBitVec entry.pc :=
    caller_query_pc_word (by dsimp [limbBase]; norm_num [timestampBase] at hp; omega) query
  have pc : entry.pc = row.start.word.toBitVec := by rw [actual, Word.ofBitVec_roundtrip]
  obtain ⟨selected, included, selectedPC, family⟩ := scope.code row member last
  have selectedSource := run_program_sources publicProgram.image selected included
  have same := path_source_instruction_unique source selectedSource (pc.trans selectedPC.symm)
  have equal : entry.data = selected.data := by
    apply Option.some.inj
    calc
      some entry.data = Delegation.Caller.decoderFields entry.instruction := source.fields.symm
      _ = Delegation.Caller.decoderFields selected.instruction := congrArg _ same
      _ = some selected.data := selectedSource.fields
  exact ⟨caller, entry, present, query, pc, (congrArg DecoderData.family equal).trans family⟩

/-- One public caller occurrence derives its complete local request/worker
    window. This uses clocks and actual PCs, not an affine program registry. -/
theorem path_caller_window [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {cut : Nat} {family : Delegation.Family}
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (image : initialImage before cells = some data.machine.initialMemory)
    (scope : PathCallerPreparation data cut family) (aligned : cut % 4 = 0) :
    8 ≤ cut ∧ ProgramCallerWindow data family (cut - 4) cut := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  obtain ⟨row, present, last⟩ := path_cycle_row size inverse accepted.toRequestChecks publicProgram
    scope.afterInitial scope.beforeTerminal aligned
  have positive := machine_native_clock_positive size inverse accepted publicProgram image present
  have floor : 8 ≤ cut := by omega
  have lowerAligned : (cut - 4) % 4 = 0 := by omega
  have count := machine_window_count size inverse accepted.toRequestChecks publicProgram lowerAligned aligned
    (by omega) (by have := scope.afterInitial; omega) scope.beforeTerminal
  have requests := request_windows size inverse accepted.toRequestChecks publicProgram lowerAligned aligned (by omega)
  have selected : ∀ one ∈ data.windowMachineRows (cut - 4) cut, one ∈ data.callers := by
    intro one included
    have member := List.mem_of_mem_filter included
    have range := of_decide_eq_true (List.mem_filter.mp included).2
    have clock := machine_clock_facts size inverse accepted.toRequestChecks publicProgram member
    exact path_caller_row_called size accepted publicProgram ordinaryProgram scope member (by omega)
  have rows : Delegation.Caller.windowCallers data.callers (cut - 4) cut =
      data.windowMachineRows (cut - 4) cut := by
    have retained : (data.windowMachineRows (cut - 4) cut).filter
        (fun one => decide (Selected one.assignment)) = data.windowMachineRows (cut - 4) cut := by
      apply List.filter_eq_self.mpr
      intro one included
      exact (List.mem_filter.mp (selected one included)).2
    simpa only [Delegation.Caller.windowCallers, RequestTrace.callers, RequestTrace.windowMachineRows,
      List.filter_filter, Bool.and_comm] using retained
  have workerCount := requests.fulfilled.length_eq
  simp only [List.length_map, rows] at workerCount
  refine ⟨floor, ⟨⟨count, rows, workerCount⟩, requests, ?_⟩⟩
  intro worker included
  obtain ⟨caller, matched, _⟩ := requests.workerMatches worker included
  have called : caller ∈ data.callers := List.mem_of_mem_filter matched.1
  have member : caller ∈ data.machine.rows := List.mem_of_mem_filter called
  have range := of_decide_eq_true (List.mem_filter.mp matched.1).2
  have clock := machine_clock_facts size inverse accepted.toRequestChecks publicProgram member
  obtain ⟨_, entry, present, query, _, family⟩ := path_caller_entry size accepted publicProgram
    ordinaryProgram scope member (by omega)
  exact (caller_worker_family (by omega) query matched.2.1).trans family

/-- The existing physical control port for each family; every other GPR port
    is a read refresh. Indirect ports remain RAM transfers. -/
def path_native_control_port : Delegation.Family → MemoryPort
  | .bigint => Bigint.importedConstraintsMemoryPorts[18]
  | .blakeG => Blake2G.importedConstraintsMemoryPorts[8]
  | .blakeRound => Blake2Round.importedConstraintsMemoryPorts[42]
  | .keccak => Keccak.importedConstraintsMemoryPorts[0]

theorem path_control_port_member (row : Delegation.Row p) :
    path_native_control_port row.family ∈ row.ports := by
  cases row with
  | mk family w =>
    cases family <;> simp [path_native_control_port, Delegation.Row.ports,
      Bigint.importedConstraintsMemoryPorts, Blake2G.importedConstraintsMemoryPorts,
      Blake2Round.importedConstraintsMemoryPorts, Keccak.importedConstraintsMemoryPorts]

theorem path_control_port_address (row : Delegation.Row p) :
    (path_native_control_port row.family).address.code row.assignment =
      (Cell.register (callerControlRegister row.family)).addressCode := by
  cases row with
  | mk family w => cases family <;> rfl

/-- Fixed native port descriptors derive the frame on every other GPR. RAM
    writes are retained and are disjoint by address space, not assumed inert. -/
theorem path_worker_register_refreshes (row : Delegation.Row p) {port : MemoryPort}
    (included : port ∈ row.ports) {register : BitVec 5}
    (different : register ≠ callerControlRegister row.family)
    (same : port.address.code row.assignment = (Cell.register register).addressCode) :
    (row.writeToken port).value = (readToken row.assignment port).value := by
  cases row with
  | mk family w =>
    cases family with
    | bigint =>
      simp [Delegation.Row.ports, Bigint.importedConstraintsMemoryPorts] at included
      rcases included with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | rfl
        | exact False.elim (different (Cell.register.inj (cell_address_injective
            (same.symm.trans (path_control_port_address (⟨.bigint, w⟩ : Delegation.Row p))))))
        | simp [MemoryAddress.code, Cell.addressCode] at same
    | blakeG =>
      simp [Delegation.Row.ports, Blake2G.importedConstraintsMemoryPorts] at included
      rcases included with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | rfl
        | exact False.elim (different (Cell.register.inj (cell_address_injective
            (same.symm.trans (path_control_port_address (⟨.blakeG, w⟩ : Delegation.Row p))))))
        | simp [MemoryAddress.code, Cell.addressCode] at same
    | blakeRound =>
      simp [Delegation.Row.ports, Blake2Round.importedConstraintsMemoryPorts] at included
      rcases included with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | rfl
        | exact False.elim (different (Cell.register.inj (cell_address_injective
            (same.symm.trans (path_control_port_address (⟨.blakeRound, w⟩ : Delegation.Row p))))))
        | simp [MemoryAddress.code, Cell.addressCode] at same
    | keccak =>
      simp [Delegation.Row.ports, Keccak.importedConstraintsMemoryPorts] at included
      rcases included with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | rfl
        | exact False.elim (different (Cell.register.inj (cell_address_injective
            (same.symm.trans (path_control_port_address (⟨.keccak, w⟩ : Delegation.Row p))))))
        | simp [MemoryAddress.code, Cell.addressCode] at same

/-- A worker has exactly one transfer at its controller GPR. This raw fact does
    not require word bounds, a round mask or any supported-controller premise. -/
theorem path_worker_control_edge (row : Delegation.Row p) {edge : MemoryToken p × MemoryToken p}
    (included : edge ∈ row.memorySteps)
    (same : edge.1.address = (Cell.register (callerControlRegister row.family)).addressCode) :
    edge = (readToken row.assignment (path_native_control_port row.family),
      row.writeToken (path_native_control_port row.family)) := by
  obtain ⟨port, present, rfl⟩ := List.mem_map.mp included
  change port.address.code row.assignment = _ at same
  cases row with
  | mk family w =>
    cases family with
    | bigint =>
      simp [Delegation.Row.ports, Bigint.importedConstraintsMemoryPorts] at present
      rcases present with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | rfl
        | simp [MemoryAddress.code, Cell.addressCode, callerControlRegister] at same
    | blakeG =>
      simp [Delegation.Row.ports, Blake2G.importedConstraintsMemoryPorts] at present
      rcases present with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | rfl
        | simp [MemoryAddress.code, Cell.addressCode, callerControlRegister] at same
    | blakeRound =>
      simp [Delegation.Row.ports, Blake2Round.importedConstraintsMemoryPorts] at present
      rcases present with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | rfl
        | simp [MemoryAddress.code, Cell.addressCode, callerControlRegister] at same
    | keccak =>
      simp [Delegation.Row.ports, Keccak.importedConstraintsMemoryPorts] at present
      rcases present with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | rfl
        | simp [MemoryAddress.code, Cell.addressCode, callerControlRegister] at same

/-- A caller cycle refreshes every GPR except its family's actual control
    register. Both machine CSR transfers are x0; native pointer reads are
    refreshes and indirect writes remain RAM effects. -/
theorem path_caller_frame_refreshes [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {cut : Nat} {family : Delegation.Family}
    {register : BitVec 5}
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (image : initialImage before cells = some data.machine.initialMemory)
    (scope : PathCallerPreparation data cut family)
    (nonzero : register ≠ 0) (different : register ≠ callerControlRegister family)
    (aligned : cut % 4 = 0) :
    ∀ edge ∈ data.windowSteps (cut - 4) cut,
      edge.1.address = (Cell.register register).addressCode → edge.2.value = edge.1.value := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  obtain ⟨_, window⟩ := path_caller_window hp inverse accepted publicProgram ordinaryProgram image scope aligned
  have requests := request_binding size inverse accepted.toRequestChecks publicProgram
  intro edge included same
  rcases List.mem_append.mp included with machine | worker
  · obtain ⟨row, selected, edgeMember⟩ := List.mem_flatMap.mp machine
    have caller : row ∈ data.callers := List.mem_of_mem_filter (window.rows.symm ▸ selected)
    obtain ⟨port, present, rfl⟩ := List.mem_map.mp edgeMember
    rw [machine_ports_caller caller] at present
    have ports : port = importedConstraintsMemoryPorts[0] ∨ port = importedConstraintsMemoryPorts[2] := by
      simpa [architecturalPorts] using present
    have binding := (requests.callers row caller).registers
    have notZero : (Cell.register 0).addressCode ≠ (Cell.register register).addressCode := by
      intro equal
      exact nonzero (Cell.register.inj (cell_address_injective equal).symm)
    rcases ports with rfl | rfl
    · exact False.elim (notZero (binding.1.symm.trans same))
    · exact False.elim (notZero (binding.2.1.symm.trans same))
  · obtain ⟨row, selected, step⟩ := List.mem_flatMap.mp worker
    obtain ⟨port, present, rfl⟩ := List.mem_map.mp step
    have sameFamily := window.family row selected
    apply path_worker_register_refreshes row (by simpa using present) _ same
    simpa only [sameFamily] using different

/-- Raw matching fixes a unique-key read before its sole write. This is list
    algebra with strict native timestamp order, without a desired-read input. -/
theorem path_single_key_read {initial terminal : List (MemoryToken p)}
    {steps : List (MemoryToken p × MemoryToken p)}
    (facts : Transfer.Facts ⟨initial, terminal, steps⟩)
    (unique : (initial.map MemoryToken.address).Nodup)
    {source : MemoryToken p} (present : source ∈ initial)
    {edge : MemoryToken p × MemoryToken p} (included : edge ∈ steps)
    (address : edge.1.address = source.address)
    (only : ∀ other ∈ steps, other.1.address = source.address → other = edge) :
    edge.1 = source := by
  have origin := facts.matching.mem_iff.mpr
    (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨edge, included, rfl⟩)))
  rcases List.mem_append.mp origin with seed | produced
  · exact List.inj_on_of_nodup_map unique seed present address
  · obtain ⟨other, member, equal⟩ := List.mem_map.mp produced
    have same : other.1.address = source.address :=
      (facts.addresses other member).trans ((congrArg MemoryToken.address equal).trans address)
    have eq := only other member same
    subst other
    have ordered := facts.order edge included
    rw [equal] at ordered
    omega

private theorem path_list_singleton {α : Type*} {rows : List α} {row : α}
    (count : rows.length = 1) (member : row ∈ rows) : rows = [row] := by
  cases rows with
  | nil => simp at member
  | cons first rest =>
    have empty : rest = [] := List.eq_nil_of_length_eq_zero (by simpa using count)
    subst rest
    have same : row = first := by simpa using member
    subst first
    rfl

/-- Actual caller and worker multiplicities make the control transfer unique
    in this occurrence's four-tick window. -/
theorem path_caller_control_edge [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {cut : Nat} {family : Delegation.Family}
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (image : initialImage before cells = some data.machine.initialMemory)
    (scope : PathCallerPreparation data cut family) (aligned : cut % 4 = 0)
    {worker : Delegation.Row p} (member : worker ∈ data.workers.windowRows (cut - 4) cut) :
    worker.family = family ∧
      (readToken worker.assignment (path_native_control_port worker.family),
        worker.writeToken (path_native_control_port worker.family)) ∈ data.windowSteps (cut - 4) cut ∧
      ∀ edge ∈ data.windowSteps (cut - 4) cut,
        edge.1.address = (Cell.register (callerControlRegister family)).addressCode →
        edge = (readToken worker.assignment (path_native_control_port worker.family),
          worker.writeToken (path_native_control_port worker.family)) := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  obtain ⟨floor, window⟩ := path_caller_window hp inverse accepted publicProgram ordinaryProgram image scope aligned
  have workerCount : (data.workers.windowRows (cut - 4) cut).length = 1 := by
    rw [← window.workerCount, window.machineCount]
    omega
  have singleton := path_list_singleton workerCount member
  have sameFamily := window.family worker member
  have requests := request_binding size inverse accepted.toRequestChecks publicProgram
  refine ⟨sameFamily, List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
    ⟨worker, member, List.mem_map.mpr ⟨_, by simpa using path_control_port_member worker, rfl⟩⟩)), ?_⟩
  intro edge included same
  rcases List.mem_append.mp included with machine | native
  · obtain ⟨row, selected, edgeMember⟩ := List.mem_flatMap.mp machine
    have caller : row ∈ data.callers := List.mem_of_mem_filter (window.rows.symm ▸ selected)
    obtain ⟨port, present, rfl⟩ := List.mem_map.mp edgeMember
    rw [machine_ports_caller caller] at present
    have ports : port = importedConstraintsMemoryPorts[0] ∨ port = importedConstraintsMemoryPorts[2] := by
      simpa [architecturalPorts] using present
    have binding := (requests.callers row caller).registers
    have notZero : (Cell.register 0).addressCode ≠
        (Cell.register (callerControlRegister family)).addressCode := by
      intro equal
      have same := Cell.register.inj (cell_address_injective equal)
      have different : (0 : BitVec 5) ≠ callerControlRegister family := by cases family <;> decide
      exact different same
    rcases ports with rfl | rfl
    · exact False.elim (notZero (binding.1.symm.trans same))
    · exact False.elim (notZero (binding.2.1.symm.trans same))
  · obtain ⟨row, selected, step⟩ := List.mem_flatMap.mp native
    have equal : row = worker := by simpa only [singleton, List.mem_singleton] using selected
    subst row
    apply path_worker_control_edge worker step
    simpa only [sameFamily] using same

/-- Raw matching derives the controller read from the earlier computed token.
    No architectural history, round mask or expected read is assumed. -/
theorem path_caller_control_read [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {cut : Nat} {family : Delegation.Family}
    {value : BitVec 32}
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (image : initialImage before cells = some data.machine.initialMemory)
    (uniqueSeeds : (data.machine.initialMemory.map MemoryToken.address).Nodup)
    (scope : PathCallerPreparation data cut family) (aligned : cut % 4 = 0)
    (seedToken : ∀ start : List (MemoryToken p),
      (data.machine.initialMemory ++ (data.prefixSteps (cut - 4)).map Prod.snd).Perm
        (start ++ (data.prefixSteps (cut - 4)).map Prod.fst) →
      ∃ token ∈ start, token.address = (Cell.register (callerControlRegister family)).addressCode ∧
        token.word = Word.ofBitVec value)
    {worker : Delegation.Row p} (member : worker ∈ data.workers.windowRows (cut - 4) cut) :
    (readToken worker.assignment (path_native_control_port worker.family)).word = Word.ofBitVec value := by
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
  obtain ⟨sameFamily, included, only⟩ := path_caller_control_edge hp inverse accepted publicProgram
    ordinaryProgram image scope aligned member
  have address : (readToken worker.assignment (path_native_control_port worker.family)).address = source.address := by
    change (path_native_control_port worker.family).address.code worker.assignment = _
    rw [path_control_port_address, sameFamily, sourceAddress]
  have equal := path_single_key_read window unique sourceMember included address
    (by intro edge present same; exact only edge present (same.trans sourceAddress))
  exact (congrArg MemoryToken.word equal).trans sourceWord

/-- Every native worker write survives to this caller's upper cut: its actual
    slot writes at cut-1 and all prefix reads precede their own earlier writes. -/
theorem path_caller_write_boundary [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {cut : Nat} {family : Delegation.Family}
    {tokens : List (MemoryToken p)}
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (image : initialImage before cells = some data.machine.initialMemory)
    (scope : PathCallerPreparation data cut family) (aligned : cut % 4 = 0)
    (matching : (data.machine.initialMemory ++ (data.prefixSteps cut).map Prod.snd).Perm
      (tokens ++ (data.prefixSteps cut).map Prod.fst))
    {worker : Delegation.Row p} (member : worker ∈ data.workers.windowRows (cut - 4) cut)
    {port : MemoryPort} (portMember : port ∈ worker.ports) :
    worker.writeToken port ∈ tokens ∧ (timeOfPair (worker.writeToken port).time).value = cut - 1 := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  obtain ⟨floor, window⟩ := path_caller_window hp inverse accepted publicProgram ordinaryProgram image scope aligned
  obtain ⟨caller, matched, _⟩ := window.requests.workerMatches worker member
  have nativeMember := List.mem_of_mem_filter (List.mem_of_mem_filter matched.1)
  have range := of_decide_eq_true (List.mem_filter.mp matched.1).2
  have clock := machine_clock_facts size inverse accepted.toRequestChecks publicProgram nativeMember
  have timestamp := matched.2.2.writes port portMember
  have last : (timeOfPair (worker.writeToken port).time).value = cut - 1 := by omega
  have requests := request_binding size inverse accepted.toRequestChecks publicProgram
  have facts := mixed_memory_facts size inverse accepted publicProgram image requests
  have edge := mixed_worker_member (List.mem_of_mem_filter member) portMember
  have inPrefix : (readToken worker.assignment port, worker.writeToken port) ∈ data.prefixSteps cut :=
    List.mem_filter.mpr ⟨edge, decide_eq_true (by change (timeOfPair (worker.writeToken port).time).value < cut; omega)⟩
  refine ⟨?_, last⟩
  have produced := matching.mem_iff.mp
    (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨_, inPrefix, rfl⟩)))
  rcases List.mem_append.mp produced with included | consumed
  · exact included
  · obtain ⟨access, selected, equal⟩ := List.mem_map.mp consumed
    have ordered := facts.order access (List.mem_of_mem_filter selected)
    have earlier := of_decide_eq_true (List.mem_filter.mp selected).2
    rw [equal, last] at ordered
    omega

private theorem path_canonical_word {word : Word} (bounded : word.Bounded) :
    Word.ofBitVec word.toBitVec = word := by
  apply Word.eq_of_value (Word.ofBitVec_bound _) bounded
  rw [Word.ofBitVec_value, Word.toBitVec_toNat bounded]

/-- Every public controller position has its exact two-limb representation.
    In particular, all ten extended-round positions are admitted. -/
theorem path_hash_word_bounded (position : HashCallPosition) : position.word.Bounded := by
  cases position with
  | mk span index =>
    cases span with
    | blakeG reduced =>
      have bound := Nat.mod_lt index.val (by cases reduced <;> decide : 0 < Blake2G.callCount reduced)
      cases reduced <;> simp only [HashCallPosition.word, Blake2G.controlAt, Blake2G.callCount,
        Bool.false_eq_true, ↓reduceIte, Word.Bounded, limbBase] at * <;> omega
    | blakeRound flags =>
      have bound := Nat.mod_lt (2 ^ index.val) (by decide : 0 < 1024)
      have flagsBound := flags.isLt
      simp only [HashCallPosition.word, Blake2Round.controlAt, Word.Bounded, limbBase]
      omega
    | keccak =>
      let control := HashCallPosition.keccakControl index
      have mode := control.mode.isLt
      have iteration := control.iteration.isLt
      have round := control.round.isLt
      change control.packed < limbBase ∧ 0 < limbBase
      dsimp [Keccak.ControlState.packed, limbBase]
      omega

theorem path_hash_word_canonical (position : HashCallPosition) :
    Word.ofBitVec position.word.toBitVec = position.word :=
  path_canonical_word (path_hash_word_bounded position)

theorem path_hash_next_word_bounded (position : HashCallPosition) : position.nextWord.Bounded := by
  cases position with
  | mk span index =>
    cases span with
    | blakeG reduced =>
      change (Blake2G.Control.step (Blake2G.controllerAt reduced index.val)).register.lo < limbBase ∧
        (Blake2G.Control.step (Blake2G.controllerAt reduced index.val)).register.hi < limbBase
      have bound := (Blake2G.controllerAt reduced index.val).register.isLt
      dsimp only [Blake2G.controllerAt] at bound
      dsimp only [Blake2G.Control.step, Blake2G.controllerAt, limbBase]
      split_ifs <;> dsimp only <;> omega
    | blakeRound flags =>
      have low := Nat.mod_lt (Blake2Round.controlAt flags index.val).hi (by decide : 0 < 8)
      have high := Nat.mod_lt ((Blake2Round.controlAt flags index.val).hi / 8) (by decide : 0 < 512)
      change 0 < limbBase ∧ _ < limbBase
      dsimp [HashCallPosition.nextWord, Blake2Round.Control.next, limbBase]
      omega
    | keccak =>
      let control := HashCallPosition.keccakControl index
      have mode := control.mode.isLt
      have iteration := control.iteration.isLt
      have round := control.round.isLt
      change control.nextPacked < limbBase ∧ 0 < limbBase
      constructor
      · dsimp [Keccak.ControlState.nextPacked, limbBase]
        split_ifs <;> omega
      · decide

/-- Local native controller equations derive the independent update for every
    G, extended-round and Keccak protocol position, before memory history or
    masks. The input binding is supplied internally by raw token matching. -/
theorem path_hash_controller_write [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    (accepted : MixedMemoryAccepted data program)
    (tables : data.workers.setup = Delegation.modeledSetup Keccak.Controller.rows)
    (position : HashCallPosition) {worker : Delegation.Row p}
    (present : worker ∈ data.workers.rows) (family : worker.family = position.span.family)
    (read : (readToken worker.assignment (path_native_control_port worker.family)).word = position.word) :
    (worker.writeToken (path_native_control_port worker.family)).word = position.nextWord := by
  cases worker with
  | mk nativeFamily w =>
    have holds := accepted.workerConstraints (⟨nativeFamily, w⟩ : Delegation.Row p) present
    have active := accepted.workerActive (⟨nativeFamily, w⟩ : Delegation.Row p) present
    cases position with
    | mk span index =>
      cases span with
      | blakeG reduced =>
        change nativeFamily = .blakeG at family
        subst nativeFamily
        change w 0 = 1 at active
        change FlatOperation.ConstraintsHoldFlat (Verification.environment w)
          (Blake2G.clockConstraints data.workers.setup.blakeG) at holds
        rw [tables] at holds
        have core : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
            (Blake2G.importedConstraints (Blake2G.setupTable Blake2G.Control.controllerRows)) :=
          Verification.holds_of_sublist holds (List.sublist_append_left _ _)
        have checked := Blake2G.Call.Proofs.controller_write (by omega : FieldCapacity.AtLeast p 512)
          (register := (Blake2G.controllerAt reduced index.val).register) core active read
        exact checked.symm
      | blakeRound flags =>
        change nativeFamily = .blakeRound at family
        subst nativeFamily
        change FlatOperation.ConstraintsHoldFlat (Verification.environment w)
          (Blake2Round.clockConstraints data.workers.setup.blakeRound) at holds
        have core : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
            (Blake2Round.importedConstraints data.workers.setup.blakeRound) :=
          Verification.holds_of_sublist holds (List.sublist_append_left _ _)
        let output : Word := ⟨(w Blake2Round.Variables.controlWriteLo).val,
          (w Blake2Round.Variables.controlWriteHi).val⟩
        have input : Blake2Round.controlAt flags index.val =
            ⟨(w Blake2Round.Variables.controlReadLo).val, (w Blake2Round.Variables.controlReadHi).val⟩ := by
          simpa [HashCallPosition.word, path_native_control_port, readToken, MemoryToken.word,
            MemoryPort.readCode, Blake2Round.importedConstraintsMemoryPorts,
            WordColumns.code, WordColumns.evaluate] using read.symm
        have checked := Blake2Round.Control.Proofs.soundness (by omega : FieldCapacity.AtLeast p 8192)
          data.workers.setup.blakeRound (Blake2Round.controlAt flags index.val) output w ⟨core, input, rfl⟩
        have projection : ((⟨.blakeRound, w⟩ : Delegation.Row p).writeToken
            Blake2Round.importedConstraintsMemoryPorts[42]).word = output := by
          simp [output, Delegation.Row.writeToken, MemoryToken.word, MemoryPort.writeCode,
            Blake2Round.importedConstraintsMemoryPorts, WordColumns.code, WordColumns.evaluate]
        exact projection.trans checked.2
      | keccak =>
        change nativeFamily = .keccak at family
        subst nativeFamily
        change w 0 = 1 at active
        change FlatOperation.ConstraintsHoldFlat (Verification.environment w)
          (Keccak.clockConstraints data.workers.setup.keccak) at holds
        rw [tables] at holds
        have core : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
            (Keccak.importedConstraints (Keccak.setupTable Keccak.Controller.rows)) :=
          Verification.holds_of_sublist holds (List.sublist_append_left _ _)
        exact Keccak.Call.Proofs.controller_write (by omega) core active read

theorem path_hash_control_register (span : Delegation.Caller.HashSpan) :
    callerControlRegister span.family = span.controlRegister := by cases span <;> rfl

theorem path_controller_dataflow_after_initial [Fact p.Prime]
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    {cut : Nat} {register : BitVec 5} {value : BitVec 32}
    (flow : PathControllerDataflow data program cut register value) :
    (timeOfPair data.machine.initial.timestamp).value + 4 ≤ cut := by
  cases flow with
  | ordinary flow => exact path_register_dataflow_after_initial flow
  | addi _ scope _ => exact scope.afterInitial
  | frame _ scope _ => exact scope.afterInitial
  | callerFrame _ scope _ => exact scope.afterInitial
  | hashAdvance _ _ scope => exact scope.afterInitial

/-- Public dataflow and native equations compute controllers across arbitrary
    actual caller/ordinary occurrences. Each call keeps its actual RAM writes,
    other GPR effects and timestamps. Hash positions include every existing
    protocol index; no supported mask or desired read is an input. -/
theorem path_controller_dataflow_token [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {cut : Nat} {register : BitVec 5} {value : BitVec 32}
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (image : initialImage before cells = some data.machine.initialMemory)
    (uniqueSeeds : (data.machine.initialMemory.map MemoryToken.address).Nodup)
    (tables : data.workers.setup = Delegation.modeledSetup Keccak.Controller.rows)
    (flow : PathControllerDataflow data program cut register value) :
    ∀ {tokens : List (MemoryToken p)}, register ≠ 0 → cut % 4 = 0 →
      (data.machine.initialMemory ++ (data.prefixSteps cut).map Prod.snd).Perm
        (tokens ++ (data.prefixSteps cut).map Prod.fst) →
      ∃ token ∈ tokens, token.address = (Cell.register register).addressCode ∧ token.word = Word.ofBitVec value := by
  induction flow with
  | ordinary flow =>
    exact path_register_dataflow_token hp inverse accepted publicProgram ordinaryProgram image uniqueSeeds flow
  | addi prior scope sourceNonzero ih =>
    intro tokens nonzero aligned matching
    have floor := path_controller_dataflow_after_initial prior
    obtain ⟨token, present, address, _, word⟩ := path_addi_token hp inverse accepted publicProgram
      ordinaryProgram image scope uniqueSeeds floor
      (fun _ prefixMatching => ih sourceNonzero (by omega) prefixMatching) nonzero aligned matching
    exact ⟨token, present, address, word⟩
  | frame prior scope form ih =>
    intro tokens nonzero aligned matching
    have floor := path_controller_dataflow_after_initial prior
    exact frame_value_token hp inverse accepted publicProgram image uniqueSeeds floor
      (fun _ prefixMatching => ih nonzero (by omega) prefixMatching) aligned
      (path_frame_refreshes hp inverse accepted publicProgram ordinaryProgram image scope form nonzero aligned) matching
  | callerFrame prior scope different ih =>
    intro tokens nonzero aligned matching
    have floor := path_controller_dataflow_after_initial prior
    exact frame_value_token hp inverse accepted publicProgram image uniqueSeeds floor
      (fun _ prefixMatching => ih nonzero (by omega) prefixMatching) aligned
      (path_caller_frame_refreshes hp inverse accepted publicProgram ordinaryProgram image scope nonzero different aligned) matching
  | @hashAdvance cut position prior scope ih =>
    intro tokens nonzero aligned matching
    obtain ⟨floor, window⟩ := path_caller_window hp inverse accepted publicProgram ordinaryProgram image scope aligned
    have count : (data.workers.windowRows (cut - 4) cut).length = 1 := by
      rw [← window.workerCount, window.machineCount]
      omega
    have notEmpty : data.workers.windowRows (cut - 4) cut ≠ [] := by
      intro empty
      rw [empty] at count
      simp at count
    obtain ⟨worker, member⟩ := List.exists_mem_of_ne_nil _ notEmpty
    have family := window.family worker member
    have source := path_caller_control_read hp inverse accepted publicProgram ordinaryProgram image uniqueSeeds
      scope aligned (value := position.word.toBitVec)
      (by
        intro start prefixMatching
        simpa only [path_hash_control_register] using ih nonzero (by omega) prefixMatching) member
    have read : (readToken worker.assignment (path_native_control_port worker.family)).word = position.word :=
      source.trans (path_canonical_word (path_hash_word_bounded position))
    have write := path_hash_controller_write hp accepted tables position (List.mem_of_mem_filter member) family read
    obtain ⟨present, _⟩ := path_caller_write_boundary hp inverse accepted publicProgram ordinaryProgram
      image scope aligned matching member (path_control_port_member worker)
    refine ⟨worker.writeToken (path_native_control_port worker.family), present, ?_, ?_⟩
    · change (path_native_control_port worker.family).address.code worker.assignment = _
      rw [path_control_port_address, family, path_hash_control_register]
    · exact write.trans (path_canonical_word (path_hash_next_word_bounded position)).symm

/-- The independent memory boundary realizes the computed controller in the
    actual state, preserving separate matching and architectural observations. -/
theorem path_controller_dataflow_at_boundary [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Clock p)
    {data : RequestTrace p} {program : List UnifiedReduced.ProgramEntry} {before atCut : State}
    {ca oa : List (BitVec 32)} {cells : List Cell} {cut : Nat} {register : BitVec 5} {value : BitVec 32}
    {tokens : List (MemoryToken p)}
    (accepted : MixedMemoryAccepted data program) (publicProgram : RequestInputs data before ca)
    (ordinaryProgram : Mixed.programImage before oa = some program)
    (image : initialImage before cells = some data.machine.initialMemory)
    (distinct : (cells.map Cell.addressCode).Nodup)
    (tables : data.workers.setup = Delegation.modeledSetup Keccak.Controller.rows)
    (flow : PathControllerDataflow data program cut register value) (nonzero : register ≠ 0)
    (aligned : cut % 4 = 0)
    (matching : (data.machine.initialMemory ++ (data.prefixSteps cut).map Prod.snd).Perm
      (tokens ++ (data.prefixSteps cut).map Prod.fst)) (boundary : NativeBoundary tokens atCut cells) :
    (Cell.register register).read atCut = .ok value atCut ∧
      ∃ token ∈ tokens, token.address = (Cell.register register).addressCode ∧ token.word = Word.ofBitVec value := by
  have unique : (data.machine.initialMemory.map MemoryToken.address).Nodup := by
    rw [image_addresses image]
    exact distinct
  obtain ⟨token, present, address, word⟩ := path_controller_dataflow_token hp inverse accepted
    publicProgram ordinaryProgram image unique tables flow nonzero aligned matching
  obtain ⟨cell, _, code, read⟩ := native_boundary_read boundary present
  have same : cell = Cell.register register := cell_address_injective (code.trans address)
  subst cell
  have bits : token.word.toBitVec = value := by rw [word, Word.ofBitVec_roundtrip]
  exact ⟨bits ▸ read, token, present, address, word⟩

end Airbender.UnifiedReduced.Caller.Proofs
