module
public import Human.Compiler.MemoryComposition
public import Proven.GKRProtocol.MemoryTokens

@[expose] public section
set_option warningAsError true

/-! The single native RAM permutation splits by address class. PC-state tokens are in address space two.
    Request tokens are virtual registers from index 32 up. Register tokens below 32 and RAM tokens are the
    memory tokens. The classes of the CPU, worker and boundary tokens give the state, request and memory
    relations of the native machine arguments. -/

namespace Airbender.Compiler.NativeMemory
open Trace Trace.Machine

/-! ### Address classes -/

/-- PC-state tokens: address space two. -/
def stateClass (token : MemoryToken babyBearModulus) : Bool := space token.address == 2

/-- Request tokens: register indices from 32 up. -/
def requestClass (token : MemoryToken babyBearModulus) : Bool :=
  space token.address == 0 && decide (32 ≤ registerIndex token.address)

/-- Register and RAM tokens: every other token. -/
def memoryClass (token : MemoryToken babyBearModulus) : Bool := !stateClass token && !requestClass token

/-- A PC-state token is in address space two. -/
theorem state_classes (state : PCState.State babyBearModulus) :
    stateClass (stateToken state) = true ∧ requestClass (stateToken state) = false ∧
      memoryClass (stateToken state) = false := by
  simp [stateClass, requestClass, memoryClass, stateToken, space]

/-- A RAM token or a register token below 32 is a memory token. -/
theorem architectural_classes {token : MemoryToken babyBearModulus} (architectural : Architectural token.address) :
    stateClass token = false ∧ requestClass token = false ∧ memoryClass token = true := by
  rcases architectural with ram | ⟨register, small⟩
  · simp [stateClass, requestClass, memoryClass, ram]
  · simp [stateClass, requestClass, memoryClass, register, small]

/-- A request token with a CSR from 32 up is a request token. -/
theorem request_classes (request : Delegation.Requests.Request babyBearModulus) (time : ZMod babyBearModulus × ZMod babyBearModulus)
    (large : 32 ≤ request.csr) :
    stateClass (request.token time) = false ∧ requestClass (request.token time) = true ∧
      memoryClass (request.token time) = false := by
  simp [stateClass, requestClass, memoryClass, Delegation.Requests.Request.token, space, registerIndex, large]

/-! ### Boundary tokens -/

/-- The register cells are registers below 32. -/
theorem register_architectural (cell : Cell) (member : cell ∈ registerCells) : Architectural cell.addressCode := by
  simp only [registerCells, List.mem_map, List.mem_range] at member
  obtain ⟨index, _, rfl⟩ := member
  right
  simp [Cell.addressCode, space, registerIndex]
  omega

/-- The initialized windows are RAM addresses. -/
theorem window_architectural (layout : InitsTeardowns.Layout) (top row : Nat) :
    Architectural (InitsTeardowns.addressCode (p := babyBearModulus) layout top row) := by
  left
  simp [InitsTeardowns.addressCode, space]

/-- The boot inputs place the seeds and the final tokens at registers below 32 and RAM. -/
theorem boot_architectural {Kind : Type} [CircuitLayout Kind] {config : RVMachineConfig}
    {trace : Data babyBearModulus Kind} {initial : RV.State} {cells : List Cell}
    {program : List RVMachineProgramEntry} {layout : InitsTeardowns.Layout}
    {inits : List (InitsTeardowns.Witness babyBearModulus layout)}
    (boot : BootInputs config trace initial cells program layout inits) :
    ∀ token ∈ trace.initialMemory ++ trace.terminalMemory, Architectural token.address := by
  intro token member
  obtain ⟨registers, addresses, terminal⟩ := boot.teardowns
  rw [boot.seeds, terminal] at member
  simp only [List.mem_append, List.mem_flatMap] at member
  rcases member with (seed | ⟨init, _, inside⟩) | (register | ⟨init, _, inside⟩)
  · simp only [registerSeeds, ROMView.nativeBootImage, List.mem_map] at seed
    obtain ⟨cell, cellMember, rfl⟩ := seed
    exact register_architectural cell cellMember
  · simp only [InitsTeardowns.Witness.initTokens, InitsTeardowns.initTokens, List.mem_flatMap, List.mem_map] at inside
    obtain ⟨top, _, row, _, rfl⟩ := inside
    exact window_architectural layout top row
  · have present : token.address ∈ registerCells.map Cell.addressCode :=
      addresses.mem_iff.mp (List.mem_map.mpr ⟨token, register, rfl⟩)
    obtain ⟨cell, cellMember, same⟩ := List.mem_map.mp present
    rw [← same]
    exact register_architectural cell cellMember
  · simp only [InitsTeardowns.Witness.teardownTokens, List.mem_flatMap, List.mem_map] at inside
    obtain ⟨⟨top, set⟩, _, row, _, rfl⟩ := inside
    exact window_architectural layout top row

/-! ### Worker tokens -/

/-- A constant register below 32, or an indirect RAM address. -/
def workerShape : MemoryAddress → Bool
  | .constantRegister index => decide (index < 32)
  | .indirect _ => true
  | _ => false

/-- A constant register below 32 and an indirect port address registers or RAM. -/
theorem shape_architectural {address : MemoryAddress} (w : Nat → ZMod babyBearModulus)
    (shape : workerShape address = true) : Architectural (address.code w) := by
  cases address with
  | constantRegister index =>
    right
    simpa [workerShape, MemoryAddress.code, space, registerIndex] using shape
  | indirect port =>
    left
    simp [MemoryAddress.code, space]
  | register => simp [workerShape] at shape
  | mixed => simp [workerShape] at shape

/-- The standard worker ports are constant registers below 32 or indirect RAM ports. -/
theorem standard_shapes (row : Delegation.Row babyBearModulus) :
    ∀ port ∈ row.ports, workerShape port.address = true := by
  have all : ∀ ports : Array MemoryPort, ports.toList.all (fun port => workerShape port.address) = true →
      ∀ port ∈ ports, workerShape port.address = true := fun ports checked port member =>
    List.all_eq_true.mp checked port (Array.mem_toList_iff.mpr member)
  obtain ⟨family, assignment⟩ := row
  cases family
  · exact all Bigint.importedConstraintsMemoryPorts (by decide +kernel)
  · exact all Blake2G.importedConstraintsMemoryPorts (by decide +kernel)
  · exact all Blake2Round.importedConstraintsMemoryPorts (by decide +kernel)
  · exact all Keccak.importedConstraintsMemoryPorts (by decide +kernel)

/-- The split worker ports are constant registers below 32 or indirect RAM ports. -/
theorem split_shapes (row : Keccak.Split.Native.Row babyBearModulus) :
    ∀ port ∈ row.ports, workerShape port.address = true := by
  have all : ∀ ports : Array MemoryPort, ports.toList.all (fun port => workerShape port.address) = true →
      ∀ port ∈ ports, workerShape port.address = true := fun ports checked port member =>
    List.all_eq_true.mp checked port (Array.mem_toList_iff.mpr member)
  obtain ⟨kind, assignment⟩ := row
  cases kind
  · exact all Keccak.Split.ColumnParity.importedConstraintsMemoryPorts (by decide +kernel)
  · exact all Keccak.Split.ThetaRho.importedConstraintsMemoryPorts (by decide +kernel)
  · exact all Keccak.Split.Chi5.importedConstraintsMemoryPorts (by decide +kernel)

/-- A standard worker request uses a CSR from 32 up. -/
theorem standard_csr (row : Delegation.Row babyBearModulus) : 32 ≤ (Delegation.Requests.fulfillment row).csr := by
  obtain ⟨family, assignment⟩ := row
  cases family <;> simp [Delegation.Requests.fulfillment, Delegation.Requests.csr]

/-- A split worker request uses a CSR from 32 up. -/
theorem split_csr (row : Keccak.Split.Native.Row babyBearModulus) : 32 ≤ (Trace.Machine.splitFulfillment row).csr := by
  obtain ⟨kind, assignment⟩ := row
  cases kind <;> simp [Trace.Machine.splitFulfillment]

/-- The classes of register and RAM tokens followed by one request token. -/
theorem ports_classes {tokens : List (MemoryToken babyBearModulus)} {request : MemoryToken babyBearModulus}
    (architectural : ∀ token ∈ tokens, Architectural token.address)
    (classes : stateClass request = false ∧ requestClass request = true ∧ memoryClass request = false) :
    (tokens ++ [request]).filter stateClass = [] ∧ (tokens ++ [request]).filter requestClass = [request] ∧
      (tokens ++ [request]).filter memoryClass = tokens := by
  have each token (member : token ∈ tokens) := architectural_classes (architectural token member)
  refine ⟨?_, ?_, ?_⟩
  · rw [List.filter_append, List.filter_eq_nil_iff.mpr (fun token member => by simp [(each token member).1])]
    simp [classes.1]
  · rw [List.filter_append, List.filter_eq_nil_iff.mpr (fun token member => by simp [(each token member).2.1])]
    simp [classes.2.1]
  · rw [List.filter_append, List.filter_eq_self.mpr (fun token member => (each token member).2.2)]
    simp [classes.2.2]

/-- The classes of the tokens of a standard worker row. -/
theorem standard_classes (row : Delegation.Row babyBearModulus) :
    (standardWrites row).filter stateClass = [] ∧
      (standardWrites row).filter requestClass = [(Delegation.Requests.fulfillment row).empty] ∧
      (standardWrites row).filter memoryClass = row.ports.toList.map row.writeToken ∧
    (standardReads row).filter stateClass = [] ∧
      (standardReads row).filter requestClass = [(Delegation.Requests.fulfillment row).issued] ∧
      (standardReads row).filter memoryClass = row.ports.toList.map (readToken row.assignment) := by
  have shapes := standard_shapes row
  have writes := ports_classes (tokens := row.ports.toList.map row.writeToken)
    (request := (Delegation.Requests.fulfillment row).empty)
    (fun token member => by
      obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp member
      exact shape_architectural row.assignment (shapes port (Array.mem_toList_iff.mp portMember)))
    (request_classes _ (0, 0) (standard_csr row))
  have reads := ports_classes (tokens := row.ports.toList.map (readToken row.assignment))
    (request := (Delegation.Requests.fulfillment row).issued)
    (fun token member => by
      obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp member
      exact shape_architectural row.assignment (shapes port (Array.mem_toList_iff.mp portMember)))
    (request_classes _ _ (standard_csr row))
  exact ⟨writes.1, writes.2.1, writes.2.2, reads.1, reads.2.1, reads.2.2⟩

/-- The classes of the tokens of a split worker row. -/
theorem split_classes (row : Keccak.Split.Native.Row babyBearModulus) :
    (splitWrites row).filter stateClass = [] ∧
      (splitWrites row).filter requestClass = [(Trace.Machine.splitFulfillment row).empty] ∧
      (splitWrites row).filter memoryClass = row.ports.toList.map row.writeToken ∧
    (splitReads row).filter stateClass = [] ∧
      (splitReads row).filter requestClass = [(Trace.Machine.splitFulfillment row).issued] ∧
      (splitReads row).filter memoryClass = row.ports.toList.map (readToken row.assignment) := by
  have shapes := split_shapes row
  have writes := ports_classes (tokens := row.ports.toList.map row.writeToken)
    (request := (Trace.Machine.splitFulfillment row).empty)
    (fun token member => by
      obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp member
      exact shape_architectural row.assignment (shapes port (Array.mem_toList_iff.mp portMember)))
    (request_classes _ (0, 0) (split_csr row))
  have reads := ports_classes (tokens := row.ports.toList.map (readToken row.assignment))
    (request := (Trace.Machine.splitFulfillment row).issued)
    (fun token member => by
      obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp member
      exact shape_architectural row.assignment (shapes port (Array.mem_toList_iff.mp portMember)))
    (request_classes _ _ (split_csr row))
  exact ⟨writes.1, writes.2.1, writes.2.2, reads.1, reads.2.1, reads.2.2⟩

/-- A flat map of singletons is a map. -/
theorem flatMap_single {α β : Type} (l : List α) (f : α → β) : l.flatMap (fun a => [f a]) = l.map f := by
  induction l <;> simp_all

/-- The classes of the tokens of all worker rows. -/
theorem worker_classes (workers : WorkerPools babyBearModulus) :
    (workerWrites workers).filter stateClass = [] ∧
      (workerWrites workers).filter requestClass = workers.fulfillments.map Delegation.Requests.Request.empty ∧
      (workerWrites workers).filter memoryClass = workers.steps.map Prod.snd ∧
    (workerReads workers).filter stateClass = [] ∧
      (workerReads workers).filter requestClass = workers.fulfillments.map Delegation.Requests.Request.issued ∧
      (workerReads workers).filter memoryClass = workers.steps.map Prod.fst := by
  simp only [workerWrites, workerReads, List.filter_append, List.filter_flatMap, WorkerPools.fulfillments,
    WorkerPools.steps, Delegation.MemoryData.steps, Keccak.Split.Native.MemoryData.steps, List.map_append,
    List.map_flatMap, Delegation.Row.memorySteps, Keccak.Split.Native.Row.memorySteps, List.map_map]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [fun row => (standard_classes row).1, fun row => (split_classes row).1]
  · simp [fun row => (standard_classes row).2.1, fun row => (split_classes row).2.1, flatMap_single, Function.comp_def]
  · simp [fun row => (standard_classes row).2.2.1, fun row => (split_classes row).2.2.1, Function.comp_def]
  · simp [fun row => (standard_classes row).2.2.2.1, fun row => (split_classes row).2.2.2.1]
  · simp [fun row => (standard_classes row).2.2.2.2.1, fun row => (split_classes row).2.2.2.2.1,
      flatMap_single, Function.comp_def]
  · simp [fun row => (standard_classes row).2.2.2.2.2, fun row => (split_classes row).2.2.2.2.2, Function.comp_def]

/-! ### CPU rows -/

/-- The classes of the tokens of one CPU row: its PC-state tokens, its request tokens when it calls a worker and
    the tokens of its architectural ports. -/
structure RowClasses {Kind : Type} [CircuitLayout Kind] (row : Row babyBearModulus Kind) (caller : Bool)
    (request : Delegation.Requests.Request babyBearModulus) (machine : Array MemoryPort) : Prop where
  writes : (cpuWrites row).filter stateClass = [stateToken row.finish] ∧
    (cpuWrites row).filter requestClass = (if caller then [request.issued] else []) ∧
    (cpuWrites row).filter memoryClass = machine.toList.map (writeToken row.columns row.assignment)
  reads : (cpuReads row).filter stateClass = [stateToken row.start] ∧
    (cpuReads row).filter requestClass = (if caller then [request.empty] else []) ∧
    (cpuReads row).filter memoryClass = machine.toList.map (readToken row.assignment)

/-- Register and RAM tokens are memory tokens only. -/
theorem architectural_filters {tokens : List (MemoryToken babyBearModulus)}
    (architectural : ∀ token ∈ tokens, Architectural token.address) :
    tokens.filter stateClass = [] ∧ tokens.filter requestClass = [] ∧ tokens.filter memoryClass = tokens :=
  ⟨List.filter_eq_nil_iff.mpr fun token member => by simp [(architectural_classes (architectural token member)).1],
    List.filter_eq_nil_iff.mpr fun token member => by simp [(architectural_classes (architectural token member)).2.1],
    List.filter_eq_self.mpr fun token member => (architectural_classes (architectural token member)).2.2⟩

/-- A row whose ports all address RAM or registers below 32 calls no worker. -/
theorem ordinary_classes {Kind : Type} [CircuitLayout Kind] (row : Row babyBearModulus Kind)
    (request : Delegation.Requests.Request babyBearModulus)
    (architectural : ∀ port ∈ row.ports, Architectural (port.address.code row.assignment)) :
    RowClasses row false request row.ports := by
  have writes := architectural_filters (tokens := row.writes) fun token member => by
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp member
    exact architectural port (Array.mem_toList_iff.mp portMember)
  have reads := architectural_filters (tokens := row.reads) fun token member => by
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp member
    exact architectural port (Array.mem_toList_iff.mp portMember)
  have finish := state_classes row.finish
  have start := state_classes row.start
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;>
    simp only [cpuWrites, cpuReads, List.filter_append, writes.1, writes.2.1, writes.2.2, reads.1, reads.2.1,
      reads.2.2, List.filter_cons, List.filter_nil, finish.1, finish.2.1, finish.2.2, start.1, start.2.1, start.2.2,
      ite_true, ite_false, Bool.false_eq_true, List.nil_append, List.append_nil] <;> rfl

/-- A caller row: its middle port carries the request tokens, its outer ports address RAM or registers below 32. -/
theorem caller_classes {Kind : Type} [CircuitLayout Kind] (row : Row babyBearModulus Kind)
    (request : Delegation.Requests.Request babyBearModulus) {first middle last : MemoryPort}
    (ports : row.ports.toList = [first, middle, last])
    (firstAddress : Architectural (first.address.code row.assignment))
    (lastAddress : Architectural (last.address.code row.assignment))
    (empty : readToken row.assignment middle = request.empty)
    (issued : writeToken row.columns row.assignment middle = request.issued) (large : 32 ≤ request.csr) :
    RowClasses row true request #[first, last] := by
  have finish := state_classes row.finish
  have start := state_classes row.start
  have issuedClasses := request_classes request request.time large
  have emptyClasses := request_classes request (0, 0) large
  have firstClasses (token : MemoryToken babyBearModulus) (same : token.address = first.address.code row.assignment) :=
    architectural_classes (same ▸ firstAddress)
  have lastClasses (token : MemoryToken babyBearModulus) (same : token.address = last.address.code row.assignment) :=
    architectural_classes (same ▸ lastAddress)
  have w0 := firstClasses (writeToken row.columns row.assignment first) rfl
  have w2 := lastClasses (writeToken row.columns row.assignment last) rfl
  have r0 := firstClasses (readToken row.assignment first) rfl
  have r2 := lastClasses (readToken row.assignment last) rfl
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;>
    simp only [cpuWrites, cpuReads, Row.writes, Row.reads, ports, List.map_cons, List.map_nil, empty, issued,
      List.cons_append, List.nil_append, List.filter_cons, finish.1, finish.2.1, finish.2.2, start.1, start.2.1,
      start.2.2, w0.1, w0.2.1, w0.2.2, w2.1, w2.2.1, w2.2.2, r0.1, r0.2.1, r0.2.2, r2.1, r2.2.1, r2.2.2,
      Delegation.Requests.Request.issued, Delegation.Requests.Request.empty, issuedClasses.1, issuedClasses.2.1,
      issuedClasses.2.2, emptyClasses.1, emptyClasses.2.1, emptyClasses.2.2, List.filter_nil, ite_true, ite_false,
      Bool.false_eq_true]

/-! ### Composition -/

/-- Flat maps agree when their functions agree on the members. -/
theorem flatMap_members {α β : Type} {l : List α} {f g : α → List β} (same : ∀ a ∈ l, f a = g a) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.flatMap_cons]
    rw [same head (List.mem_cons_self ..), ih fun a member => same a (List.mem_cons_of_mem _ member)]

/-- A flat map of optional singletons is a map of the selected members. -/
theorem flatMap_selected {α β : Type} (l : List α) (selected : α → Bool) (f : α → β) :
    l.flatMap (fun a => if selected a then [f a] else []) = (l.filter selected).map f := by
  induction l with
  | nil => rfl
  | cons head tail ih => cases h : selected head <;> simp_all

/-- The CPU steps of the architectural ports `machine`. -/
def machineSteps {Kind : Type} [CircuitLayout Kind] (rows : List (Row babyBearModulus Kind))
    (machine : Row babyBearModulus Kind → Array MemoryPort) : List (MemoryToken babyBearModulus × MemoryToken babyBearModulus) :=
  rows.flatMap fun row => (machine row).toList.map fun port =>
    (readToken row.assignment port, writeToken row.columns row.assignment port)

/-- The address classes of both sides of the single RAM permutation. -/
theorem production_classes {Kind : Type} [CircuitLayout Kind] (trace : Data babyBearModulus Kind)
    (workers : WorkerPools babyBearModulus) (caller : Row babyBearModulus Kind → Bool)
    (request : Row babyBearModulus Kind → Delegation.Requests.Request babyBearModulus)
    (machine : Row babyBearModulus Kind → Array MemoryPort)
    (boundary : ∀ token ∈ trace.initialMemory ++ trace.terminalMemory, Architectural token.address)
    (rows : ∀ row ∈ trace.rows, RowClasses row (caller row) (request row) (machine row)) :
    let writes := stateToken trace.initial :: trace.initialMemory ++ trace.rows.flatMap cpuWrites ++
      workerWrites workers
    let reads := stateToken trace.terminal :: trace.terminalMemory ++ trace.rows.flatMap cpuReads ++
      workerReads workers
    writes.filter stateClass = (trace.initial :: trace.rows.map Row.finish).map stateToken ∧
    reads.filter stateClass = (trace.terminal :: trace.rows.map Row.start).map stateToken ∧
    writes.filter requestClass = ((trace.rows.filter caller).map request).map Delegation.Requests.Request.issued ++
      workers.fulfillments.map Delegation.Requests.Request.empty ∧
    reads.filter requestClass = ((trace.rows.filter caller).map request).map Delegation.Requests.Request.empty ++
      workers.fulfillments.map Delegation.Requests.Request.issued ∧
    writes.filter memoryClass = trace.initialMemory ++ (machineSteps trace.rows machine ++ workers.steps).map Prod.snd ∧
    reads.filter memoryClass = trace.terminalMemory ++ (machineSteps trace.rows machine ++ workers.steps).map Prod.fst := by
  intro writes reads
  have initial := architectural_filters fun token member => boundary token (List.mem_append_left _ member)
  have terminal := architectural_filters fun token member => boundary token (List.mem_append_right _ member)
  have workerClasses := worker_classes workers
  have initialState := state_classes trace.initial
  have terminalState := state_classes trace.terminal
  have writeRows (c : MemoryToken babyBearModulus → Bool) (g : Row babyBearModulus Kind → List (MemoryToken babyBearModulus))
      (each : ∀ row ∈ trace.rows, (cpuWrites row).filter c = g row) :
      (trace.rows.flatMap cpuWrites).filter c = trace.rows.flatMap g := by
    rw [List.filter_flatMap]
    exact flatMap_members each
  have readRows (c : MemoryToken babyBearModulus → Bool) (g : Row babyBearModulus Kind → List (MemoryToken babyBearModulus))
      (each : ∀ row ∈ trace.rows, (cpuReads row).filter c = g row) :
      (trace.rows.flatMap cpuReads).filter c = trace.rows.flatMap g := by
    rw [List.filter_flatMap]
    exact flatMap_members each
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [writes, List.filter_append, List.filter_cons, initialState.1, ite_true, initial.1, workerClasses.1,
      List.append_nil, writeRows stateClass (fun row => [stateToken row.finish]) fun row member => (rows row member).writes.1,
      flatMap_single, List.cons_append, List.nil_append, List.map_cons, List.map_map, Function.comp_def]
  · simp only [reads, List.filter_append, List.filter_cons, terminalState.1, ite_true, terminal.1,
      workerClasses.2.2.2.1, List.append_nil,
      readRows stateClass (fun row => [stateToken row.start]) fun row member => (rows row member).reads.1,
      flatMap_single, List.cons_append, List.nil_append, List.map_cons, List.map_map, Function.comp_def]
  · simp only [writes, List.filter_append, List.filter_cons, initialState.2.1, Bool.false_eq_true, ite_false,
      initial.2.1, workerClasses.2.1, List.nil_append,
      writeRows requestClass (fun row => if caller row then [(request row).issued] else [])
        fun row member => (rows row member).writes.2.1,
      flatMap_selected, List.map_map, Function.comp_def]
  · simp only [reads, List.filter_append, List.filter_cons, terminalState.2.1, Bool.false_eq_true, ite_false,
      terminal.2.1, workerClasses.2.2.2.2.1, List.nil_append,
      readRows requestClass (fun row => if caller row then [(request row).empty] else [])
        fun row member => (rows row member).reads.2.1,
      flatMap_selected, List.map_map, Function.comp_def]
  · simp only [writes, List.filter_append, List.filter_cons, initialState.2.2, Bool.false_eq_true, ite_false,
      initial.2.2, workerClasses.2.2.1,
      writeRows memoryClass (fun row => (machine row).toList.map (writeToken row.columns row.assignment))
        fun row member => (rows row member).writes.2.2]
    simp [machineSteps, List.map_flatMap, List.map_map, Function.comp_def, List.append_assoc]
  · simp only [reads, List.filter_append, List.filter_cons, terminalState.2.2, Bool.false_eq_true, ite_false,
      terminal.2.2, workerClasses.2.2.2.2.2,
      readRows memoryClass (fun row => (machine row).toList.map (readToken row.assignment))
        fun row member => (rows row member).reads.2.2]
    simp [machineSteps, List.map_flatMap, List.map_map, Function.comp_def, List.append_assoc]

/-- A request token is not a PC-state token. -/
theorem request_not_state {token : MemoryToken babyBearModulus} (request : requestClass token = true) :
    stateClass token = false := by
  simp only [requestClass, Bool.and_eq_true, beq_iff_eq] at request
  simp [stateClass, request.1]

/-- Every token list is the concatenation of its three address classes, up to order. -/
theorem partition (tokens : List (MemoryToken babyBearModulus)) :
    tokens.Perm (tokens.filter stateClass ++ tokens.filter requestClass ++ tokens.filter memoryClass) := by
  have outer := (List.filter_append_perm stateClass tokens).symm
  have inner := (List.filter_append_perm requestClass (tokens.filter fun token => !stateClass token)).symm
  have requests : (tokens.filter fun token => !stateClass token).filter requestClass = tokens.filter requestClass := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro token _
    cases h : requestClass token
    · simp
    · simp [request_not_state h]
  have memory : (tokens.filter fun token => !stateClass token).filter (fun token => !requestClass token) =
      tokens.filter memoryClass := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro token _
    simp [memoryClass, Bool.and_comm]
  rw [List.append_assoc]
  exact outer.trans (List.Perm.append_left _ (by rw [← requests, ← memory]; exact inner))

/-- The single RAM permutation holds exactly when its three address classes match: the PC states, the requests
    and the architectural memory. -/
theorem production_iff {Kind : Type} [CircuitLayout Kind] (trace : Data babyBearModulus Kind)
    (workers : WorkerPools babyBearModulus) (caller : Row babyBearModulus Kind → Bool)
    (request : Row babyBearModulus Kind → Delegation.Requests.Request babyBearModulus)
    (machine : Row babyBearModulus Kind → Array MemoryPort)
    (boundary : ∀ token ∈ trace.initialMemory ++ trace.terminalMemory, Architectural token.address)
    (rows : ∀ row ∈ trace.rows, RowClasses row (caller row) (request row) (machine row)) :
    RamPermutation trace workers ↔
      (trace.initial :: trace.rows.map Row.finish).Perm (trace.terminal :: trace.rows.map Row.start) ∧
      Delegation.Requests.Matching ((trace.rows.filter caller).map request) workers.fulfillments ∧
      (trace.initialMemory ++ (machineSteps trace.rows machine ++ workers.steps).map Prod.snd).Perm
        (trace.terminalMemory ++ (machineSteps trace.rows machine ++ workers.steps).map Prod.fst) := by
  obtain ⟨sw, sr, rw', rr, mw, mr⟩ := production_classes trace workers caller request machine boundary rows
  constructor
  · intro production
    refine ⟨?_, ?_, ?_⟩
    · have states := production.filter stateClass
      rw [sw, sr] at states
      simpa [List.map_map, Function.comp_def, state_token_left_inverse] using states.map tokenState
    · have requests := production.filter requestClass
      rw [rw', rr] at requests
      exact requests
    · have memory := production.filter memoryClass
      rw [mw, mr] at memory
      exact memory
  · rintro ⟨states, requests, memory⟩
    refine (partition _).trans (List.Perm.trans ?_ (partition _).symm)
    rw [sw, sr, rw', rr, mw, mr]
    exact ((states.map stateToken).append requests).append memory

/-! ### Caller rows -/

/-- Every caller family uses a CSR from 32 up. -/
theorem family_csr (family : Delegation.Family) : 32 ≤ Delegation.Requests.csr family := by
  cases family <;> decide

/-- An unrolled CPU row calls a worker when it is an ADD/SUB row with the caller selector. -/
abbrev unrolledCaller (row : Row babyBearModulus PooledFamily) : Bool :=
  row.family == .addSub && decide (Delegation.Requests.Selected row.assignment)

/-- The classes of the tokens of an unrolled CPU row. The binding of a caller gives its request tokens. -/
theorem unrolled_row_classes (row : Row babyBearModulus PooledFamily)
    (binding : unrolledCaller row = true → ∃ (before : RV.State) (callers : List Delegation.Caller.RVProgramEntry),
      Delegation.Caller.RVBinding row.assignment before callers)
    (machine : ∀ port ∈ Delegation.Caller.machinePorts row, Architectural (port.address.code row.assignment)) :
    RowClasses row (unrolledCaller row) (Delegation.Requests.caller row.assignment)
      (Delegation.Caller.machinePorts row) := by
  cases selected : unrolledCaller row
  · have ordinary : Delegation.Caller.machinePorts row = row.ports := ite_eq_right (by simpa using selected)
    rw [ordinary] at machine ⊢
    exact ordinary_classes row _ machine
  · obtain ⟨before, callers, bound⟩ := binding selected
    obtain ⟨entry, _, _, _, _, csr⟩ := bound.instruction
    have caller : Delegation.Caller.machinePorts row = Delegation.Caller.architecturalPorts := ite_eq_left selected
    rw [caller] at machine ⊢
    obtain ⟨family, assignment⟩ := row
    obtain rfl : family = .addSub := by simpa using (Bool.and_eq_true _ _).mp selected |>.1
    exact caller_classes _ _ (first := AddSub.importedConstraintsMemoryPorts[0])
      (middle := Delegation.Requests.callerPort) (last := AddSub.importedConstraintsMemoryPorts[2])
      (show AddSub.importedConstraintsMemoryPorts.toList = _ by decide +kernel)
      (machine _ (by simp [Delegation.Caller.architecturalPorts]))
      (machine _ (by simp [Delegation.Caller.architecturalPorts]))
      bound.emptyRead bound.issuedWrite (csr ▸ family_csr _)

/-- A unified CPU row calls a worker when it has the caller selector. -/
abbrev unifiedCaller (row : Row babyBearModulus UnifiedFamily) : Bool :=
  decide (UnifiedReduced.Caller.Selected row.assignment)

/-- The classes of the tokens of a unified CPU row. The binding of a caller gives its request tokens. -/
theorem unified_row_classes (row : Row babyBearModulus UnifiedFamily)
    (binding : UnifiedReduced.Caller.Selected row.assignment →
      ∃ (before : RV.State) (callers : List Delegation.Caller.RVProgramEntry),
        UnifiedReduced.Caller.RVBinding row.assignment before callers)
    (machine : ∀ port ∈ UnifiedReduced.Caller.machinePorts row, Architectural (port.address.code row.assignment)) :
    RowClasses row (unifiedCaller row) (UnifiedReduced.Caller.request row.assignment)
      (UnifiedReduced.Caller.machinePorts row) := by
  cases selected : unifiedCaller row
  · have ordinary : UnifiedReduced.Caller.machinePorts row = row.ports := ite_eq_right (by simpa using selected)
    rw [ordinary] at machine ⊢
    exact ordinary_classes row _ machine
  · obtain ⟨before, callers, bound⟩ := binding (by simpa using selected)
    obtain ⟨entry, _, _, _, csr, _⟩ := bound.instruction
    have caller : UnifiedReduced.Caller.machinePorts row = UnifiedReduced.Caller.architecturalPorts :=
      ite_eq_left (by simpa using selected)
    rw [caller] at machine ⊢
    obtain ⟨family, assignment⟩ := row
    cases family
    exact caller_classes _ _ (first := UnifiedReduced.importedConstraintsMemoryPorts[0])
      (middle := UnifiedReduced.Caller.virtualPort) (last := UnifiedReduced.importedConstraintsMemoryPorts[2])
      (show UnifiedReduced.importedConstraintsMemoryPorts.toList = _ by decide +kernel)
      (machine _ (by simp [UnifiedReduced.Caller.architecturalPorts]))
      (machine _ (by simp [UnifiedReduced.Caller.architecturalPorts]))
      bound.virtual.1 bound.virtual.2 (csr ▸ family_csr _)

/-- A Boolean test of `Architectural`. -/
def architecturalCheck (address : Nat) : Bool :=
  space address == 1 || (space address == 0 && decide (registerIndex address < 32))

/-- The Boolean test gives `Architectural`. -/
theorem architectural_of_check {address : Nat} (checked : architecturalCheck address = true) :
    Architectural address := by
  simp only [architecturalCheck, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at checked
  exact checked

/-- A kernel check of every port address gives the address classes of the ports. -/
theorem ports_architectural {ports : Array MemoryPort} {w : Nat → ZMod babyBearModulus}
    (checked : ports.toList.all (fun port => architecturalCheck (port.address.code w)) = true) :
    ∀ port ∈ ports, Architectural (port.address.code w) := fun port member =>
  architectural_of_check (List.all_eq_true.mp checked port (Array.mem_toList_iff.mpr member))

end Airbender.Compiler.NativeMemory
