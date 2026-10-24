import Tests.PathGLoopProgram
import Airbender.Proofs.Trace.FiniteFootprint
import Airbender.Proofs.Blake2G.Control
import Airbender.Proofs.Blake2G.ArtifactChecks
import Airbender.Review.Trace.UnifiedReduced.MixedMemory
import Airbender.Review.Trace.UnifiedReduced.NativeMixedROM

namespace Tests.PathGLoopNative
open Airbender Trace Arithmetic Reference.RiscV.Sail Reference.Sail PathGLoopProgram
set_option warningAsError true
set_option Elab.async false

/-- Every GPR, both complete sixteen-word blocks, and a separate scratch word. -/
def cells : List Cell :=
  (List.finRange 32).map (fun i => .register (BitVec.ofNat 5 i.val)) ++
  (List.finRange 16).map (fun i => .ram (stateAddress + BitVec.ofNat 32 (4 * i.val))) ++
  (List.finRange 16).map (fun i => .ram (messageAddress + BitVec.ofNat 32 (4 * i.val))) ++
  [.ram scratchAddress]

def isCaller (index : Fin 228) : Bool := decide ((rowCodeIndex index).val = 6 ∨ (rowCodeIndex index).val = 11)
def isStore (variant : Variant) (index : Fin 228) : Bool := decide (index.val = 226 ∧ variant ≠ .baseline)
def isBranch (index : Fin 228) : Bool := decide ((rowCodeIndex index).val = 9)
def isJal (index : Fin 228) : Bool := decide ((rowCodeIndex index).val = 5 ∨ (rowCodeIndex index).val = 7)
def iteration (index : Fin 228) : Nat := (index.val - 6) / 4

def metadata (variant : Variant) (index : Fin 228) : DecoderData UnifiedFamily :=
  if isCaller index then (Tests.DelegationCaller.entry .blakeG).data.mapFamily (fun _ => .machine)
  else (UnifiedReduced.decoderFields (codeEntry variant (rowCodeIndex index)).instruction).getD
    ⟨.machine, 0, 0, 0, ⟨0, 0⟩, 0, 0⟩

def machineClock (index : Fin 228) : Nat := 4 + 4 * index.val

def nextPC (index : Fin 228) : Nat :=
  if index.val < 5 then 4 * (index.val + 1)
  else if index.val = 5 then 128
  else if index.val < 226 then
    match (index.val - 6) % 4 with
    | 0 => 132 | 1 => 144 | 2 => 148 | _ => if iteration index < 54 then 128 else 152
  else if index.val = 226 then 156 else 160

def source0 (variant : Variant) (index : Fin 228) : Nat :=
  if index.val = 1 then stateAddress.toNat
  else if index.val < 6 then 0
  else if index.val < 226 then
    if (index.val - 6) % 4 = 2 then 55 - iteration index
    else if (index.val - 6) % 4 = 3 then 54 - iteration index else 0
  else if index.val = 226 then
    match variant with
    | .baseline => 7 | .scratch => stateAddress.toNat | .protectedMessage => messageAddress.toNat
  else 0

def source1 (variant : Variant) (index : Fin 228) : Nat := if isStore variant index then 7 else 0

def oldDestination (variant : Variant) (index : Fin 228) : Nat :=
  if index.val < 6 then 0
  else if index.val < 226 then
    if (index.val - 6) % 4 = 1 then if iteration index = 0 then 0 else 136
    else if (index.val - 6) % 4 = 2 then 55 - iteration index else 0
  else if index.val = 226 ∧ variant = .baseline then 7 else 0

def newDestination (_variant : Variant) (index : Fin 228) : Nat :=
  if index.val = 0 then stateAddress.toNat
  else if index.val = 1 then messageAddress.toNat
  else if index.val = 2 then 128
  else if index.val = 3 then 55
  else if index.val = 4 then 7
  else if index.val < 226 then
    if (index.val - 6) % 4 = 1 then 136
    else if (index.val - 6) % 4 = 2 then 54 - iteration index else 0
  else if index.val = 226 then 7 else 0

def storeAddress (variant : Variant) : BitVec 32 :=
  if variant = .scratch then scratchAddress else messageAddress

def machineCells (variant : Variant) (index : Fin 228) : Vector Cell 3 :=
  let fields := metadata variant index
  #v[.register fields.rs1, .register fields.rs2,
    if isStore variant index then .ram (storeAddress variant) else .register fields.rd]

/-- A concrete chronological ledger used to construct candidate predecessor
clocks and endpoint tokens. Equality with the actual imported native transfers
is proved separately; no matching or successful execution is assumed here. -/
structure Write where
  cell : Cell
  stamp : Nat
  value : Word

def machineWrites (variant : Variant) (index : Fin 228) : List Write :=
  let port := machineCells variant index
  let clock := machineClock index
  let first : Write := ⟨port[0], clock, Word.ofBitVec (BitVec.ofNat 32 (source0 variant index))⟩
  let second : Write := ⟨port[1], clock + 1, Word.ofBitVec (BitVec.ofNat 32 (source1 variant index))⟩
  let last : Write := ⟨port[2], clock + 2, Word.ofBitVec (BitVec.ofNat 32 (newDestination variant index))⟩
  if isCaller index then [first, last] else [first, second, last]

def workerCells (index : Fin 56) : Vector Cell 9 :=
  let control := Blake2G.Control.step (Blake2G.controllerAt true index.val)
  #v[.register 10,
    .ram (stateAddress + BitVec.ofNat 32 (4 * control.stateOffsets[0])),
    .ram (stateAddress + BitVec.ofNat 32 (4 * control.stateOffsets[1])),
    .ram (stateAddress + BitVec.ofNat 32 (4 * control.stateOffsets[2])),
    .ram (stateAddress + BitVec.ofNat 32 (4 * control.stateOffsets[3])),
    .register 11,
    .ram (messageAddress + BitVec.ofNat 32 (4 * control.messageOffsets[0])),
    .ram (messageAddress + BitVec.ofNat 32 (4 * control.messageOffsets[1])),
    .register 12]

def workerValue (index : Fin 56) (port : Fin 9) : Word :=
  if port.val = 0 then Word.ofBitVec stateAddress
  else if port.val = 5 then Word.ofBitVec messageAddress
  else if port.val = 8 then (Blake2G.Control.step (Blake2G.controllerAt true index.val)).register
  else ⟨0, 0⟩

def workerWrites (index : Fin 56) : List Write :=
  (List.finRange 9).map fun port => ⟨(workerCells index)[port], callStart index + 3, workerValue index port⟩

def rowWrites (variant : Variant) (index : Fin 228) : List Write :=
  machineWrites variant index ++
    if active : index.val < 226 ∧ (index.val - 6) % 4 = 0 ∧ 6 ≤ index.val then
      workerWrites ⟨iteration index, by dsimp [iteration]; have := index.isLt; omega⟩
    else if index.val = 227 then workerWrites 55 else []

def prefixWrites (variant : Variant) (count : Nat) : List Write :=
  (List.finRange count).flatMap fun index =>
    if bound : index.val < 228 then rowWrites variant ⟨index.val, bound⟩ else []

def lastStamp (writes : List Write) (cell : Cell) : Nat :=
  writes.foldl (fun stamp write => if write.cell = cell then write.stamp else stamp) 0

def previous (variant : Variant) (index : Fin 228) (port : Fin 3) : Nat :=
  if isCaller index ∧ port.val = 1 then 0
  else lastStamp (prefixWrites variant index.val ++
    (machineWrites variant index).filter fun write => decide (write.stamp < machineClock index + port.val))
    ((machineCells variant index)[port])

/-- Candidate complete unified rows with every decoder, effect and clock
column retained. Their actual imported equations and queries are later checks. -/
def machineAssignment (variant : Variant) (index : Fin 228) (column : Nat) : ZMod babyBearModulus :=
  let fields := metadata variant index
  let code := codeEntry variant (rowCodeIndex index)
  let family2 := isBranch index || isJal index
  let taken := isBranch index && decide (iteration index < 54)
  let saved := if isBranch index then source0 variant index else code.pc.toNat + 4
  if column = 0 then code.pc.toNat
  else if column = 2 then machineClock index
  else if column = 4 ∨ column = 130 ∨ column = 131 ∨ column = 132 ∨ column = 133 then 1
  else if column = 5 then fields.rs1.toNat
  else if column = 6 then if isCaller index then 0x7c8 else fields.rs2.toNat
  else if column = 7 then fields.rd.toNat
  else if column = 8 then fields.immediate.lo
  else if column = 9 then fields.immediate.hi
  else if column = 10 then fields.funct3
  else if 11 ≤ column ∧ column ≤ 29 then if fields.mask.testBit (column - 11) then 1 else 0
  else if column = 30 then nextPC index
  else if column = 32 then machineClock index + 4
  else if column = 34 then previous variant index 0
  else if column = 36 then (source0 variant index % 65536 : Nat)
  else if column = 37 then (source0 variant index / 65536 : Nat)
  else if column = 38 then if isCaller index then 0x7c8 else fields.rs2.toNat
  else if column = 40 then previous variant index 1
  else if column = 42 then (source1 variant index % 65536 : Nat)
  else if column = 43 then (source1 variant index / 65536 : Nat)
  else if column = 44 then if isStore variant index then (Word.ofBitVec (storeAddress variant)).lo else fields.rd.toNat
  else if column = 45 then if isStore variant index then (Word.ofBitVec (storeAddress variant)).hi else 0
  else if column = 46 then previous variant index 2
  else if column = 48 then (oldDestination variant index % 65536 : Nat)
  else if column = 49 then (oldDestination variant index / 65536 : Nat)
  else if column = 50 then (newDestination variant index % 65536 : Nat)
  else if column = 51 then (newDestination variant index / 65536 : Nat)
  else if column = 52 ∨ column = 53 then if (rowCodeIndex index).val = 8 then 1 else 0
  else if column = 54 ∨ column = 55 then if taken then 1 else 0
  else if column = 57 then if isStore variant index then (Word.ofBitVec (storeAddress variant)).lo
    else if isBranch index && !taken then 1 else 0
  else if column = 58 then if isStore variant index then 512 else 0
  else if column = 59 ∨ column = 82 ∨ column = 112 then if taken then 1 else 0
  else if column = 78 then
    if isStore variant index then ((Word.ofBitVec (storeAddress variant)).lo / 4 : Nat)
    else if family2 then saved else 0
  else if column = 80 then (source0 variant index : ZMod babyBearModulus) * source1 variant index * 943718400
  else if column = 81 ∨ column = 120 ∨ column = 122 then if family2 then nextPC index else 0
  else if column = 83 then if (rowCodeIndex index).val = 7 then 1 else 0
  else if column = 85 then if family2 && decide ((rowCodeIndex index).val ≠ 7) then 1 else 0
  else if column = 86 then if isStore variant index then 448 else 0
  else if column = 88 then if family2 then 1 else 0
  else if column = 89 then if family2 then saved else 0
  else if column = 90 then if isBranch index && !taken then 1 else 0
  else if column = 92 ∨ column = 101 then if family2 then 5 else 0
  else if column = 110 then if family2 then 51 else 0
  else if column = 111 then if isBranch index then if taken then 16 else 24 else 0
  else if column = 119 then if family2 then 2 else 0
  else if column = 129 then if family2 then 0 else 1
  else 0

def workerReadStamp (variant : Variant) (index : Fin 56) (port : Fin 9) : Nat :=
  lastStamp (prefixWrites variant (callRow index).val ++ machineWrites variant (callRow index))
    ((workerCells index)[port])

/-- Zero arithmetic with the pinned controller's actual selected addresses.
Read clocks come from the same chronological candidate ledger as CPU rows. -/
def workerAssignment (variant : Variant) (index : Fin 56) (column : Nat) : ZMod babyBearModulus :=
  let control := Blake2G.Control.step (Blake2G.controllerAt true index.val)
  if column = 0 then 1
  else if column = 1 then callStart index + 1
  else if column = 3 then (Blake2G.controlAt true index.val).lo
  else if column = 5 then control.register.lo
  else if stateOffset : 7 ≤ column ∧ column < 11 then control.stateOffsets[column - 7]'(by omega)
  else if messageOffset : 11 ≤ column ∧ column < 13 then control.messageOffsets[column - 11]'(by omega)
  else if column = 14 ∨ column = 32 then 512
  else if column = 31 then 64
  else if column = 83 then 31457280
  else if timestamp : 84 ≤ column ∧ column < 111 then
    if (column - 84) % 3 = 0 then workerReadStamp variant index ⟨(column - 84) / 3, by omega⟩
    else if (column - 84) % 3 = 2 then 1 else 0
  else 0

def machineRows (variant : Variant) : List (Row babyBearModulus UnifiedFamily) :=
  (List.finRange 228).map fun index => ⟨.machine, machineAssignment variant index⟩

def workerRows (variant : Variant) : List (Delegation.Row babyBearModulus) :=
  (List.finRange 56).map fun index => ⟨.blakeG, workerAssignment variant index⟩

def old (cell : Cell) : MemoryToken babyBearModulus := cell.initialToken 0

def final (variant : Variant) (cell : Cell) : MemoryToken babyBearModulus :=
  (prefixWrites variant 228).foldl (fun token write =>
    if write.cell = cell then ⟨cell.addressCode, (write.stamp, 0), Nat.pair write.value.lo write.value.hi⟩ else token)
    (old cell)

/-- Candidate native data only. Actual acceptance, exact matching, public
initialization, complete path preparation and execution are subsequent proofs. -/
noncomputable def data (variant : Variant) : UnifiedReduced.Caller.RequestTrace babyBearModulus where
  machine := {
    rows := machineRows variant
    rom := UnifiedReduced.Setup.table (before variant)
    initial := PCState.boundary 0 (4, 0)
    terminal := PCState.boundary 160 (916, 0)
    initialMemory := cells.map old
    terminalMemory := cells.map (final variant) }
  workers := ⟨Delegation.modeledSetup Keccak.Controller.rows, workerRows variant, [], []⟩
  program := callerProgram

theorem machine_count (variant : Variant) : (data variant).machine.rows.length = 228 := by
  simp only [data, machineRows, List.length_map, List.length_finRange]

theorem worker_count (variant : Variant) : (data variant).workers.rows.length = 56 := by
  simp only [data, workerRows, List.length_map, List.length_finRange]

/- Symbolic ledger algebra. Only the finite physical cell domain is traversed;
   the complete token permutation will telescope actual chronological writes. -/
private theorem ledger_commute_middle {α : Type*} (front middle back : List α) :
    ((front ++ middle) ++ back).Perm ((front ++ back) ++ middle) := by
  simpa only [List.append_assoc] using
    (List.perm_append_comm (l₁ := middle) (l₂ := back)).append_left front

private theorem ledger_balance_compose {α : Type*}
    {initial middle final readsOne readsTwo writesOne writesTwo : List α}
    (one : (initial ++ writesOne).Perm (middle ++ readsOne))
    (two : (middle ++ writesTwo).Perm (final ++ readsTwo)) :
    (initial ++ (writesOne ++ writesTwo)).Perm (final ++ (readsOne ++ readsTwo)) := by
  have first := one.append_right writesTwo
  have last := two.append_right readsOne
  simpa only [List.append_assoc] using first.trans
    ((ledger_commute_middle _ _ _).trans (last.trans (ledger_commute_middle _ _ _)))

private theorem ledger_balance_update {α β : Type*} [DecidableEq α]
    (domain : List α) (distinct : domain.Nodup) (start : α → β) (cell : α)
    (member : cell ∈ domain) (value : β) :
    (domain.map start ++ [value]).Perm
      (domain.map (Function.update start cell value) ++ [start cell]) := by
  apply Trace.FiniteFootprint.balance_of_nodup domain [cell] start
    (Function.update start cell value) [start cell] [value] distinct (by simp)
  · intro selected present
    have same := List.mem_singleton.mp present
    exact same.symm ▸ member
  · intro other _ outside
    have different : other ≠ cell := by simpa only [List.mem_singleton] using outside
    simp only [Function.update_of_ne different]
  · simpa only [List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      Function.update_self] using
        (List.perm_append_comm (l₁ := [start cell]) (l₂ := [value]))

private def writeTokenOf (write : Write) : MemoryToken babyBearModulus :=
  ⟨write.cell.addressCode, (write.stamp, 0), Nat.pair write.value.lo write.value.hi⟩

private def ledgerPut (start : Cell → MemoryToken babyBearModulus) (write : Write) :=
  Function.update start write.cell (writeTokenOf write)

private def ledgerRun (start : Cell → MemoryToken babyBearModulus) (writes : List Write) :=
  writes.foldl ledgerPut start

private def ledgerReads (start : Cell → MemoryToken babyBearModulus) :
    List Write → List (MemoryToken babyBearModulus)
  | [] => []
  | write :: rest => start write.cell :: ledgerReads (ledgerPut start write) rest

private theorem ledger_balance (domain : List Cell) (distinct : domain.Nodup)
    (writes : List Write) (members : ∀ write ∈ writes, write.cell ∈ domain)
    (start : Cell → MemoryToken babyBearModulus) :
    (domain.map start ++ writes.map writeTokenOf).Perm
      (domain.map (ledgerRun start writes) ++ ledgerReads start writes) := by
  induction writes generalizing start with
  | nil => exact List.Perm.refl _
  | cons write rest ih =>
      have first := ledger_balance_update domain distinct start write.cell
        (members write (by simp)) (writeTokenOf write)
      have later := ih (fun item member => members item (by simp [member])) (ledgerPut start write)
      simpa only [ledgerRun, List.foldl_cons, List.map_cons, ledgerReads, ledgerPut,
        List.singleton_append] using ledger_balance_compose first later

/-- The candidate endpoint is exactly the symbolic update fold, with no
assumed terminal value or supplied read token. -/
private theorem ledger_final (variant : Variant) :
    ledgerRun old (prefixWrites variant 228) = final variant := by
  have fold (writes : List Write) (start : Cell → MemoryToken babyBearModulus) (cell : Cell) :
      (writes.foldl ledgerPut start) cell = writes.foldl
        (fun token write => if write.cell = cell then
          ⟨cell.addressCode, (write.stamp, 0), Nat.pair write.value.lo write.value.hi⟩ else token)
        (start cell) := by
    induction writes generalizing start with
    | nil => rfl
    | cons write rest ih =>
        rw [List.foldl_cons, List.foldl_cons, ih]
        congr 1
        by_cases equal : write.cell = cell
        · subst cell
          simp only [ledgerPut, Function.update_self, if_true, writeTokenOf]
        · simp only [ledgerPut, Function.update_of_ne (Ne.symm equal), equal, if_false]
  funext cell
  change ((prefixWrites variant 228).foldl ledgerPut old) cell =
    (prefixWrites variant 228).foldl
      (fun token write => if write.cell = cell then
        ⟨cell.addressCode, (write.stamp, 0), Nat.pair write.value.lo write.value.hi⟩ else token)
      (old cell)
  exact fold (prefixWrites variant 228) old cell

private theorem machine_write_clock_bound (variant : Variant) (index : Fin 228)
    {write : Write} (member : write ∈ machineWrites variant index) : write.stamp < 916 := by
  have bound := index.isLt
  dsimp only [machineWrites] at member
  split_ifs at member
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> dsimp only [machineClock] <;> omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> dsimp only [machineClock] <;> omega

private theorem worker_write_clock_bound (index : Fin 56)
    {write : Write} (member : write ∈ workerWrites index) : write.stamp < 916 := by
  obtain ⟨port, _, rfl⟩ := List.mem_map.mp member
  change callStart index + 3 < 916
  unfold callStart
  have bound := (callRow index).isLt
  omega

private theorem row_write_clock_bound (variant : Variant) (index : Fin 228)
    {write : Write} (member : write ∈ rowWrites variant index) : write.stamp < 916 := by
  dsimp only [rowWrites] at member
  rcases List.mem_append.mp member with machine | worker
  · exact machine_write_clock_bound variant index machine
  · split_ifs at worker with active last
    · exact worker_write_clock_bound _ worker
    · exact worker_write_clock_bound _ worker
    · cases worker

private theorem last_stamp_fold_bound (writes : List Write) (cell : Cell)
    (stamp : Nat) (small : stamp < 916)
    (bounds : ∀ write ∈ writes, write.stamp < 916) :
    writes.foldl (fun value write => if write.cell = cell then write.stamp else value) stamp < 916 := by
  induction writes generalizing stamp with
  | nil => exact small
  | cons write rest ih =>
      apply ih
      · dsimp only
        split_ifs
        · exact bounds write (by simp)
        · exact small
      · intro item member; exact bounds item (by simp [member])

private theorem prefix_previous_bound (variant : Variant) (count : Nat) (cell : Cell) :
    lastStamp (prefixWrites variant count) cell < 916 := by
  apply last_stamp_fold_bound _ cell 0 (by decide)
  intro write member
  unfold prefixWrites at member
  obtain ⟨index, _, member⟩ := List.mem_flatMap.mp member
  split_ifs at member with bound
  · exact row_write_clock_bound variant _ member
  · cases member

/-- The actual imported G invocation columns contain the selected caller's
clock plus one; this is a projection of the concrete assignment. -/
theorem worker_invocation (variant : Variant) (index : Fin 56) :
    rawPair (workerAssignment variant index) Blake2G.importedConstraintsDelegationColumns.invocation =
      ((callStart index + 1 : Nat), 0) := by
  simp [Blake2G.importedConstraintsDelegationColumns, rawPair, workerAssignment]

/-- The native controller read and write limbs match the actual indexed
controller transition, including the final reduced call's wrap to128. -/
theorem worker_control (variant : Variant) (index : Fin 56) :
    (readToken (workerAssignment variant index) Blake2G.importedConstraintsMemoryPorts[8]).word =
        Blake2G.controlAt true index.val ∧
      ((⟨.blakeG, workerAssignment variant index⟩ : Delegation.Row babyBearModulus).writeToken
        Blake2G.importedConstraintsMemoryPorts[8]).word =
        (Blake2G.Control.step (Blake2G.controllerAt true index.val)).register := by
  have before : (Blake2G.controlAt true index.val).lo < babyBearModulus := by
    change 128 + index.val % 56 < babyBearModulus
    have bound := Nat.mod_lt index.val (by decide : 0 < 56)
    dsimp [babyBearModulus]; omega
  have after := Blake2G.Control.Proofs.controller_bounded (Blake2G.controllerAt true index.val).key 0
  rw [Blake2G.Control.Proofs.controller_input] at after
  change (Blake2G.Control.step (Blake2G.controllerAt true index.val)).register.lo < 256 at after
  have canonical : (Blake2G.Control.step (Blake2G.controllerAt true index.val)).register.lo < babyBearModulus := by
    dsimp [babyBearModulus]; omega
  have high : (Blake2G.Control.step (Blake2G.controllerAt true index.val)).register.hi = 0 := by
    unfold Blake2G.Control.step
    split <;> rfl
  simp [Blake2G.importedConstraintsMemoryPorts, readToken, Delegation.Row.writeToken,
    Delegation.Row.columns, rawPair, MemoryPort.readCode, MemoryPort.writeCode,
    WordColumns.code, WordColumns.evaluate, MemoryToken.word, workerAssignment,
    ZMod.val_natCast_of_lt before, ZMod.val_natCast_of_lt canonical]
  constructor
  · rfl
  · exact congrArg
      (fun upper => Word.mk (Blake2G.Control.step (Blake2G.controllerAt true index.val)).register.lo upper)
      high.symm

/-- The scheduled reduced controller satisfies the added native guard, including
the final wrap from 183 to 128. -/
private theorem worker_control_guard : ∀ index : Fin 56,
    let read : ZMod babyBearModulus := (Blake2G.controlAt true index.val).lo
    let written : ZMod babyBearModulus :=
      (Blake2G.Control.step (Blake2G.controllerAt true index.val)).register.lo
    (read + 1 - written) * (16 * (read + 1 - written) - 1280 + 3 * written) = 0 := by
  decide +kernel

/-- Every polynomial equation in the actual imported native G row is checked
with its real assignment. Lookup membership is a separate later proof. -/
theorem worker_equations (variant : Variant) (index : Fin 56) :
    ∀ expression ∈ FlatOperation.constraints
      (Blake2G.importedConstraints (Blake2G.setupTable Blake2G.Control.controllerRows)),
      expression.eval (Verification.environment (workerAssignment variant index)) = 0 := by
  rw [List.forall_mem_iff_forall_getElem]
  intro equation bound
  have short : equation < 34 := by simpa only [Blake2G.constraint_count] using bound
  by_cases guard : equation = 11
  · subst equation
    dsimp only [Blake2G.importedConstraints, FlatOperation.constraints]
    simp only [List.getElem_cons_zero, List.getElem_cons_succ]
    norm_num [Expression.eval, Verification.environment, workerAssignment, -mul_eq_zero]
    convert worker_control_guard index using 1
    ring
  interval_cases equation
  all_goals try contradiction
  all_goals dsimp only [Blake2G.importedConstraints, FlatOperation.constraints]
  all_goals simp only [List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals norm_num [Expression.eval, Verification.environment, workerAssignment,
    babyBearModulus]
  all_goals decide +kernel

/-- The participating CPU row's actual imported execute column is one. -/
theorem machine_active (variant : Variant) (index : Fin 228) :
    (⟨.machine, machineAssignment variant index⟩ : Row babyBearModulus UnifiedFamily).assignment
      (⟨.machine, machineAssignment variant index⟩ : Row babyBearModulus UnifiedFamily).columns.execute = 1 := by
  change machineAssignment variant index 4 = 1
  simp [machineAssignment]

/-- The actual imported CPU clock limbs retain the four-tick stride. -/
theorem machine_native_timing (variant : Variant) (index : Fin 228) :
    rawPair (machineAssignment variant index) UnifiedReduced.importedConstraintsTraceColumns.initialTime =
        ((machineClock index : Nat), 0) ∧
      rawPair (machineAssignment variant index) UnifiedReduced.importedConstraintsTraceColumns.finalTime =
        ((machineClock index + 4 : Nat), 0) := by
  simp [UnifiedReduced.importedConstraintsTraceColumns, rawPair, machineAssignment]


/- Value/time projections of the chronological ledger and exact grouping of
   all native CPU/worker steps. No matching or accepted witness is assumed. -/

private def wordPut (start : Cell → Word) (write : Write) : Cell → Word :=
  Function.update start write.cell write.value

private def wordRun (start : Cell → Word) (writes : List Write) : Cell → Word :=
  writes.foldl wordPut start

private theorem wordRun_append (start : Cell → Word) (one two : List Write) :
    wordRun start (one ++ two) = wordRun (wordRun start one) two := by
  exact List.foldl_append

private theorem wordPut_refresh (start : Cell → Word) (write : Write)
    (same : start write.cell = write.value) : wordPut start write = start := by
  funext cell
  by_cases equal : cell = write.cell
  · subst cell; simpa only [wordPut, Function.update_self] using same.symm
  · simp only [wordPut, Function.update_of_ne equal]

private theorem wordRun_refreshes (start : Cell → Word) (writes : List Write)
    (refreshes : ∀ write ∈ writes, start write.cell = write.value) :
    wordRun start writes = start := by
  revert refreshes
  induction writes with
  | nil => intro _; rfl
  | cons write rest ih =>
      intro refreshes
      change wordRun (wordPut start write) rest = start
      rw [wordPut_refresh start write (refreshes write (by simp))]
      exact ih (fun item member => refreshes item (by simp [member]))

private theorem wordRun_cpu_three (start : Cell → Word) (first second last : Write)
    (readFirst : start first.cell = first.value) (readSecond : start second.cell = second.value) :
    wordRun start [first, second, last] = Function.update start last.cell last.value := by
  change wordPut (wordPut (wordPut start first) second) last = _
  rw [wordPut_refresh start first readFirst, wordPut_refresh start second readSecond]
  rfl

private theorem wordRun_cpu_two (start : Cell → Word) (first last : Write)
    (readFirst : start first.cell = first.value) :
    wordRun start [first, last] = Function.update start last.cell last.value := by
  change wordPut (wordPut start first) last = _
  rw [wordPut_refresh start first readFirst]
  rfl

private theorem ledger_word_run (start : Cell → MemoryToken babyBearModulus) (writes : List Write) :
    (fun cell => (ledgerRun start writes cell).word) =
      wordRun (fun cell => (start cell).word) writes := by
  induction writes generalizing start with
  | nil => rfl
  | cons write rest ih =>
      have seed : (fun cell => (ledgerPut start write cell).word) =
          wordPut (fun cell => (start cell).word) write := by
        funext cell
        by_cases equal : cell = write.cell
        · subst cell
          simp only [ledgerPut, wordPut, Function.update_self, writeTokenOf,
            MemoryToken.word, Nat.unpair_pair]
        · simp only [ledgerPut, wordPut, Function.update_of_ne equal]
      change (fun cell => (ledgerRun (ledgerPut start write) rest cell).word) =
        wordRun (wordPut (fun cell => (start cell).word) write) rest
      rw [ih (ledgerPut start write), seed]

private theorem ledger_time_run (start : Cell → MemoryToken babyBearModulus) (writes : List Write) :
    ∀ cell, (ledgerRun start writes cell).time =
      writes.foldl
        (fun time write => if write.cell = cell then ((write.stamp : ZMod babyBearModulus), 0) else time)
        (start cell).time := by
  induction writes generalizing start with
  | nil => intro cell; rfl
  | cons write rest ih =>
      intro cell
      change (ledgerRun (ledgerPut start write) rest cell).time =
        rest.foldl
          (fun time write => if write.cell = cell then ((write.stamp : ZMod babyBearModulus), 0) else time)
          (if write.cell = cell then ((write.stamp : ZMod babyBearModulus), 0) else (start cell).time)
      rw [ih (ledgerPut start write) cell]
      apply congrArg (fun seed => rest.foldl
        (fun time write => if write.cell = cell then ((write.stamp : ZMod babyBearModulus), 0) else time) seed)
      by_cases equal : write.cell = cell
      · subst cell
        simp only [ledgerPut, Function.update_self, writeTokenOf]
        rfl
      · simp only [ledgerPut, Function.update_of_ne (Ne.symm equal), if_neg equal]

private theorem prefixWrites_succ (variant : Variant) (count : Nat) (bound : count < 228) :
    prefixWrites variant (count + 1) =
      prefixWrites variant count ++ rowWrites variant ⟨count, bound⟩ := by
  unfold prefixWrites
  rw [List.finRange_succ_last, List.flatMap_append, List.flatMap_map]
  simp only [Fin.val_castSucc, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, Fin.val_last, dif_pos bound]

private theorem prefix_words_succ (variant : Variant) (count : Nat) (bound : count < 228) :
    wordRun (fun cell => (old cell).word) (prefixWrites variant (count + 1)) =
      wordRun (wordRun (fun cell => (old cell).word) (prefixWrites variant count))
        (rowWrites variant ⟨count, bound⟩) := by
  rw [prefixWrites_succ variant count bound, wordRun_append]


private theorem flatMap_interleaving {α β : Type*} (items : List α)
    (first second : α → List β) :
    (items.flatMap (fun item => first item ++ second item)).Perm
      (items.flatMap first ++ items.flatMap second) := by
  induction items with
  | nil => exact List.Perm.refl _
  | cons item rest ih =>
      have tail := ih.append_left (first item ++ second item)
      have commute := ((List.perm_append_comm (l₁ := second item)
        (l₂ := rest.flatMap first)).append_left (first item)).append_right (rest.flatMap second)
      have reorder : ((first item ++ second item) ++
          (rest.flatMap first ++ rest.flatMap second)).Perm
          ((first item ++ rest.flatMap first) ++ (second item ++ rest.flatMap second)) := by
        simpa only [List.append_assoc] using commute
      simpa only [List.flatMap_cons] using tail.trans reorder

private def rowWorkers (index : Fin 228) : List (Fin 56) :=
  if active : index.val < 226 ∧ (index.val - 6) % 4 = 0 ∧ 6 ≤ index.val then
    [⟨iteration index, by dsimp [iteration]; have := index.isLt; omega⟩]
  else if index.val = 227 then [55] else []

private theorem worker_occurrence_indices :
    (List.finRange 228).flatMap rowWorkers = List.finRange 56 := by
  decide +kernel

private def nativeMachineSteps (variant : Variant) (index : Fin 228) :=
  let row : Row babyBearModulus UnifiedFamily := ⟨.machine, machineAssignment variant index⟩
  (UnifiedReduced.Caller.machinePorts row).toList.map fun port =>
    (readToken row.assignment port, writeToken row.columns row.assignment port)

private def nativeWorkerSteps (variant : Variant) (index : Fin 56) :=
  (⟨.blakeG, workerAssignment variant index⟩ : Delegation.Row babyBearModulus).memorySteps

private def chronologicalNativeSteps (variant : Variant) :=
  (List.finRange 228).flatMap fun index =>
    nativeMachineSteps variant index ++ (rowWorkers index).flatMap (nativeWorkerSteps variant)

/-- All real CPU/worker accesses are retained. This is only a grouping
permutation; timestamp refreshes and actual JAL register writes stay present. -/
private theorem native_interleaving (variant : Variant) :
    (chronologicalNativeSteps variant).Perm (data variant).mixedSteps := by
  have interleaving := flatMap_interleaving (List.finRange 228)
    (nativeMachineSteps variant) (fun index => (rowWorkers index).flatMap (nativeWorkerSteps variant))
  have workers : (List.finRange 228).flatMap
      (fun index => (rowWorkers index).flatMap (nativeWorkerSteps variant)) =
        (List.finRange 56).flatMap (nativeWorkerSteps variant) := by
    rw [← List.flatMap_assoc, worker_occurrence_indices]
  rw [workers] at interleaving
  have nativeData : (data variant).mixedSteps =
      (List.finRange 228).flatMap (nativeMachineSteps variant) ++
        (List.finRange 56).flatMap (nativeWorkerSteps variant) := by
    simp only [data, machineRows, workerRows, UnifiedReduced.Caller.RequestTrace.mixedSteps,
      Delegation.MemoryData.steps, List.flatMap_map]
    congr 1
  rw [nativeData]
  exact interleaving

private theorem row_ledger_writes (variant : Variant) (index : Fin 228) :
    rowWrites variant index =
      machineWrites variant index ++ (rowWorkers index).flatMap workerWrites := by
  dsimp only [rowWrites, rowWorkers]
  split_ifs <;> simp

private theorem chronological_ledger_writes (variant : Variant) :
    prefixWrites variant 228 =
      (List.finRange 228).flatMap fun index =>
        machineWrites variant index ++ (rowWorkers index).flatMap workerWrites := by
  unfold prefixWrites
  apply List.flatMap_congr
  intro index _
  rw [dif_pos index.isLt, row_ledger_writes]



/- Scalar word-state invariants for the actual indexed G controller and
   chronological worker writes. Native read-token identity remains a later proof. -/

private def wordOfNat (value : Nat) : Word := Word.ofBitVec (BitVec.ofNat 32 value)

private theorem wordOfNat_small {value : Nat} (bound : value < 65536) :
    wordOfNat value = ⟨value, 0⟩ := by
  have whole : value < 2 ^ 32 := Nat.lt_trans bound (by decide)
  simp only [wordOfNat, Word.ofBitVec, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt whole, limbBase, Nat.mod_eq_of_lt bound, Nat.div_eq_of_lt bound]

private def loopWords (control counter link : Nat) (stored : Option (BitVec 32)) : Cell → Word
  | .register register =>
      if register = 10 then Word.ofBitVec stateAddress
      else if register = 11 then Word.ofBitVec messageAddress
      else if register = 12 then wordOfNat control
      else if register = 5 then wordOfNat counter
      else if register = 1 then wordOfNat link
      else if register = 2 then wordOfNat 7 else ⟨0, 0⟩
  | .ram address => if stored = some address then wordOfNat 7 else ⟨0, 0⟩

private theorem loopWords_zero (control counter link : Nat) (stored : Option (BitVec 32)) :
    loopWords control counter link stored (.register 0) = ⟨0, 0⟩ := by
  simp [loopWords]

private theorem loopWords_control (control counter link next : Nat) (stored : Option (BitVec 32)) :
    Function.update (loopWords control counter link stored) (.register 12) (wordOfNat next) =
      loopWords next counter link stored := by
  funext cell
  cases cell with
  | register register =>
      by_cases selected : register = BitVec.ofNat 5 12
      · subst register; simp [loopWords]
      · simp [Function.update, loopWords, selected]
  | ram address => simp [Function.update, loopWords]

private theorem loopWords_counter (control counter link next : Nat) (stored : Option (BitVec 32)) :
    Function.update (loopWords control counter link stored) (.register 5) (wordOfNat next) =
      loopWords control next link stored := by
  funext cell
  cases cell with
  | register register =>
      by_cases selected : register = BitVec.ofNat 5 5
      · subst register; simp [loopWords]
      · simp [Function.update, loopWords, selected]
  | ram address => simp [Function.update, loopWords]

private theorem loopWords_link (control counter link next : Nat) (stored : Option (BitVec 32)) :
    Function.update (loopWords control counter link stored) (.register 1) (wordOfNat next) =
      loopWords control counter next stored := by
  funext cell
  cases cell with
  | register register =>
      by_cases selected : register = BitVec.ofNat 5 1
      · subst register; simp [loopWords]
      · simp [Function.update, loopWords, selected]
  | ram address => simp [Function.update, loopWords]

theorem loop_row_index (index : Fin 55) (phase : Fin 4) :
    rowCodeIndex ⟨6 + 4 * index.val + phase.val, by have := index.isLt; have := phase.isLt; omega⟩ =
      (⟨6 + phase.val, by have := phase.isLt; omega⟩ : Fin 12) := by
  apply Fin.ext
  dsimp [rowCodeIndex]
  have small := index.isLt
  have offset := phase.isLt
  split_ifs <;> omega

private theorem loop_call_row (index : Fin 55) :
    callRow ⟨index.val, by have := index.isLt; omega⟩ =
      (⟨6 + 4 * index.val, by have := index.isLt; omega⟩ : Fin 228) := by
  apply Fin.ext
  simp only [callRow, index.isLt, ↓reduceIte]

private theorem next_control (index : Fin 56) :
    (Blake2G.Control.step (Blake2G.controllerAt true index.val)).register =
      Blake2G.controlAt true (index.val + 1) := by
  fin_cases index <;> rfl

/-- These are only native chronological values. CPU/worker token identity and
query membership are kept as additional proof obligations, not premises here. -/
private theorem worker_word_run (index : Fin 56) (counter link : Nat) :
    wordRun (loopWords (128 + index.val) counter link none) (workerWrites index) =
      loopWords (128 + (index.val + 1) % 56) counter link none := by
  let start := loopWords (128 + index.val) counter link none
  let makeWrite (port : Fin 9) : Write :=
    ⟨(workerCells index)[port], callStart index + 3, workerValue index port⟩
  have refreshes : ∀ port : Fin 8, start (makeWrite port.castSucc).cell = (makeWrite port.castSucc).value := by
    intro port
    fin_cases port <;> simp [start, makeWrite, workerCells, workerValue, loopWords]
  have unchanged : wordRun start ((List.finRange 8).map fun port => makeWrite port.castSucc) = start := by
    apply wordRun_refreshes
    intro write member
    obtain ⟨port, _, rfl⟩ := List.mem_map.mp member
    exact refreshes port
  have cell : (makeWrite 8).cell = .register 12 := rfl
  have value : (makeWrite 8).value = wordOfNat (128 + (index.val + 1) % 56) := by
    change (Blake2G.Control.step (Blake2G.controllerAt true index.val)).register = _
    rw [next_control]
    have small : 128 + (index.val + 1) % 56 < 65536 := by
      have := Nat.mod_lt (index.val + 1) (by decide : 0 < 56); omega
    rw [wordOfNat_small small]
    rfl
  change wordRun start ((List.finRange 9).map makeWrite) = _
  rw [List.finRange_succ_last, List.map_append, List.map_map, wordRun_append]
  change wordRun
    (wordRun start ((List.finRange 8).map fun port => makeWrite port.castSucc)) [makeWrite 8] = _
  rw [unchanged]
  change Function.update start (makeWrite 8).cell (makeWrite 8).value = _
  rw [cell, value]
  exact loopWords_control _ _ _ _ _



/- Actual chronological prefix word states: public boot assignments,55loop
   iterations, variant-specific final store, and the final indexed G call. -/

def gapRow (index : Fin 55) (phase : Fin 4) : Fin 228 :=
  ⟨6 + 4 * index.val + phase.val, by have := index.isLt; have := phase.isLt; omega⟩

theorem gap_caller (index : Fin 55) (phase : Fin 4) :
    isCaller (gapRow index phase) = decide (phase.val = 0) := by
  have code : rowCodeIndex (gapRow index phase) =
      (⟨6 + phase.val, by have := phase.isLt; omega⟩ : Fin 12) := loop_row_index index phase
  unfold isCaller
  rw [code]
  fin_cases phase <;> rfl

private theorem gap_not_store (variant : Variant) (index : Fin 55) (phase : Fin 4) :
    isStore variant (gapRow index phase) = false := by
  have different : (gapRow index phase).val ≠ 226 := by
    dsimp [gapRow]
    have := index.isLt
    have := phase.isLt
    omega
  simp [isStore, different]

private theorem loop_row_zero (variant : Variant) (index : Fin 55) (counter link : Nat) :
    wordRun (loopWords (128 + index.val) counter link none) (rowWrites variant (gapRow index 0)) =
      loopWords (129 + index.val) counter link none := by
  have control := worker_word_run ⟨index.val, by have := index.isLt; omega⟩ counter link
  have indexBound := index.isLt
  have active : (gapRow index 0).val < 226 ∧ ((gapRow index 0).val - 6) % 4 = 0 ∧
      6 ≤ (gapRow index 0).val := by dsimp [gapRow]; omega
  have loopIndex : iteration (gapRow index 0) = index.val := by dsimp [iteration, gapRow]; omega
  have first : source0 variant (gapRow index 0) = 0 := by
    dsimp [source0, gapRow, iteration]; split_ifs <;> omega
  have last : newDestination variant (gapRow index 0) = 0 := by
    dsimp [newDestination, gapRow, iteration]; split_ifs <;> omega
  have cells : machineCells variant (gapRow index 0) = #v[.register 0, .register 0, .register 0] := by
    simp [machineCells, metadata, gap_caller, gap_not_store, Tests.DelegationCaller.entry,
      DecoderData.mapFamily]
  rw [rowWrites, dif_pos active, wordRun_append]
  have unchanged : wordRun (loopWords (128 + index.val) counter link none)
      (machineWrites variant (gapRow index 0)) = loopWords (128 + index.val) counter link none := by
    apply wordRun_refreshes
    intro write member
    simp only [machineWrites, cells, gap_caller, first, last] at member
    rcases List.mem_cons.mp member with rfl | remaining
    · rfl
    · rcases List.mem_singleton.mp remaining with rfl
      rfl
  rw [unchanged]
  simpa only [loopIndex, Nat.mod_eq_of_lt (show index.val + 1 < 56 by omega),
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using control

private theorem loop_row_jal (variant : Variant) (index : Fin 55) (link : Nat) :
    wordRun (loopWords (129 + index.val) (55 - index.val) link none)
      (rowWrites variant (gapRow index 1)) =
      loopWords (129 + index.val) (55 - index.val) 136 none := by
  have code : rowCodeIndex (gapRow index 1) = 7 := loop_row_index index 1
  have small := index.isLt
  have noWorker : ¬ ((gapRow index 1).val < 226 ∧ ((gapRow index 1).val - 6) % 4 = 0 ∧
      6 ≤ (gapRow index 1).val) := by dsimp [gapRow]; omega
  have notLast : (gapRow index 1).val ≠ 227 := by dsimp [gapRow]; omega
  simp only [rowWrites, dif_neg noWorker, if_neg notLast, List.append_nil]
  have cells : machineCells variant (gapRow index 1) = #v[.register 0, .register 0, .register 1] := by
    simp [machineCells, metadata, gap_caller, gap_not_store]
    simp only [code]
    exact ⟨rfl, rfl, rfl⟩
  have last : newDestination variant (gapRow index 1) = 136 := by
    dsimp [newDestination, gapRow]; split_ifs <;> omega
  have first : source0 variant (gapRow index 1) = 0 := by
    dsimp [source0, gapRow]; split_ifs <;> omega
  have second : source1 variant (gapRow index 1) = 0 := by
    simp [source1, gap_not_store]
  have writes : machineWrites variant (gapRow index 1) =
      [⟨.register 0, machineClock (gapRow index 1), wordOfNat 0⟩,
       ⟨.register 0, machineClock (gapRow index 1) + 1, wordOfNat 0⟩,
       ⟨.register 1, machineClock (gapRow index 1) + 2, wordOfNat 136⟩] := by
    simp [machineWrites, cells, gap_caller, first, second, last, wordOfNat]
  rw [writes]
  rw [wordRun_cpu_three _ _ _ _ (by rfl) (by rfl)]
  exact loopWords_link _ _ _ _ _

private theorem loop_row_decrement (variant : Variant) (index : Fin 55) :
    wordRun (loopWords (129 + index.val) (55 - index.val) 136 none)
      (rowWrites variant (gapRow index 2)) =
      loopWords (129 + index.val) (54 - index.val) 136 none := by
  have code : rowCodeIndex (gapRow index 2) = 8 := loop_row_index index 2
  have small := index.isLt
  have noWorker : ¬ ((gapRow index 2).val < 226 ∧ ((gapRow index 2).val - 6) % 4 = 0 ∧
      6 ≤ (gapRow index 2).val) := by dsimp [gapRow]; omega
  have notLast : (gapRow index 2).val ≠ 227 := by dsimp [gapRow]; omega
  simp only [rowWrites, dif_neg noWorker, if_neg notLast, List.append_nil]
  have cells : machineCells variant (gapRow index 2) = #v[.register 5, .register 0, .register 5] := by
    simp [machineCells, metadata, gap_caller, gap_not_store]
    simp only [code]
    exact ⟨rfl, rfl, rfl⟩
  have first : source0 variant (gapRow index 2) = 55 - index.val := by
    dsimp [source0, gapRow, iteration]; split_ifs <;> omega
  have second : source1 variant (gapRow index 2) = 0 := by
    simp [source1, gap_not_store]
  have last : newDestination variant (gapRow index 2) = 54 - index.val := by
    dsimp [newDestination, gapRow, iteration]; split_ifs <;> omega
  have writes : machineWrites variant (gapRow index 2) =
      [⟨.register 5, machineClock (gapRow index 2), wordOfNat (55 - index.val)⟩,
       ⟨.register 0, machineClock (gapRow index 2) + 1, wordOfNat 0⟩,
       ⟨.register 5, machineClock (gapRow index 2) + 2, wordOfNat (54 - index.val)⟩] := by
    simp [machineWrites, cells, gap_caller, first, second, last, wordOfNat]
  rw [writes]
  rw [wordRun_cpu_three _ _ _ _ (by rfl) (by rfl)]
  exact loopWords_counter _ _ _ _ _

private theorem loop_row_branch (variant : Variant) (index : Fin 55) :
    wordRun (loopWords (129 + index.val) (54 - index.val) 136 none)
      (rowWrites variant (gapRow index 3)) =
      loopWords (129 + index.val) (54 - index.val) 136 none := by
  have code : rowCodeIndex (gapRow index 3) = 9 := loop_row_index index 3
  have small := index.isLt
  have noWorker : ¬ ((gapRow index 3).val < 226 ∧ ((gapRow index 3).val - 6) % 4 = 0 ∧
      6 ≤ (gapRow index 3).val) := by dsimp [gapRow]; omega
  have notLast : (gapRow index 3).val ≠ 227 := by dsimp [gapRow]; omega
  simp only [rowWrites, dif_neg noWorker, if_neg notLast, List.append_nil]
  have cells : machineCells variant (gapRow index 3) = #v[.register 5, .register 0, .register 0] := by
    simp [machineCells, metadata, gap_caller, gap_not_store]
    simp only [code]
    exact ⟨rfl, rfl, rfl⟩
  have first : source0 variant (gapRow index 3) = 54 - index.val := by
    dsimp [source0, gapRow, iteration]; split_ifs <;> omega
  have second : source1 variant (gapRow index 3) = 0 := by
    simp [source1, gap_not_store]
  have last : newDestination variant (gapRow index 3) = 0 := by
    dsimp [newDestination, gapRow, iteration]; split_ifs <;> omega
  apply wordRun_refreshes
  intro write member
  simp only [machineWrites, cells, gap_caller, first, second, last] at member
  rcases List.mem_cons.mp member with rfl | remaining
  · rfl
  · rcases List.mem_cons.mp remaining with rfl | remaining
    · rfl
    · rcases List.mem_singleton.mp remaining with rfl
      rfl

private theorem loop_words_iteration (variant : Variant) (index : Fin 55) (link : Nat) :
    wordRun (loopWords (128 + index.val) (55 - index.val) link none)
      (rowWrites variant (gapRow index 0) ++ rowWrites variant (gapRow index 1) ++
       rowWrites variant (gapRow index 2) ++ rowWrites variant (gapRow index 3)) =
      loopWords (128 + (index.val + 1)) (55 - (index.val + 1)) 136 none := by
  simp only [List.append_assoc]
  rw [wordRun_append, loop_row_zero, wordRun_append, loop_row_jal,
    wordRun_append, loop_row_decrement, loop_row_branch]
  congr 1 <;> omega

private theorem loop_boot_words (variant : Variant) :
    wordRun (fun cell => (old cell).word) (prefixWrites variant 6) = loopWords 128 55 0 none := by
  have writes : prefixWrites variant 6 =
      [⟨.register 0, 4, wordOfNat 0⟩, ⟨.register 0, 5, wordOfNat 0⟩,
       ⟨.register 10, 6, Word.ofBitVec stateAddress⟩,
       ⟨.register 10, 8, Word.ofBitVec stateAddress⟩, ⟨.register 0, 9, wordOfNat 0⟩,
       ⟨.register 11, 10, Word.ofBitVec messageAddress⟩,
       ⟨.register 0, 12, wordOfNat 0⟩, ⟨.register 0, 13, wordOfNat 0⟩,
       ⟨.register 12, 14, wordOfNat 128⟩,
       ⟨.register 0, 16, wordOfNat 0⟩, ⟨.register 0, 17, wordOfNat 0⟩,
       ⟨.register 5, 18, wordOfNat 55⟩,
       ⟨.register 0, 20, wordOfNat 0⟩, ⟨.register 0, 21, wordOfNat 0⟩,
       ⟨.register 2, 22, wordOfNat 7⟩,
       ⟨.register 0, 24, wordOfNat 0⟩, ⟨.register 0, 25, wordOfNat 0⟩,
       ⟨.register 0, 26, wordOfNat 0⟩] := by rfl
  have registers (bits : Fin 32) :
      wordRun (fun cell => (old cell).word) (prefixWrites variant 6)
          (.register (BitVec.ofNat 5 bits.val)) =
        loopWords 128 55 0 none (.register (BitVec.ofNat 5 bits.val)) := by
    rw [writes]
    fin_cases bits <;> rfl
  funext cell
  cases cell with
  | register register => simpa using registers register.toFin
  | ram address => rw [writes]; rfl

private theorem prefixWrites_four (variant : Variant) (first : Nat) (bound : first + 3 < 228) :
    prefixWrites variant (first + 4) =
      prefixWrites variant first ++
        (rowWrites variant ⟨first, by omega⟩ ++
         rowWrites variant ⟨first + 1, by omega⟩ ++
         rowWrites variant ⟨first + 2, by omega⟩ ++
         rowWrites variant ⟨first + 3, bound⟩) := by
  have step3 : prefixWrites variant (first + 4) =
      prefixWrites variant (first + 3) ++ rowWrites variant ⟨first + 3, bound⟩ :=
    prefixWrites_succ variant (first + 3) bound
  have step2 : prefixWrites variant (first + 3) =
      prefixWrites variant (first + 2) ++ rowWrites variant ⟨first + 2, by omega⟩ :=
    prefixWrites_succ variant (first + 2) (by omega)
  have step1 : prefixWrites variant (first + 2) =
      prefixWrites variant (first + 1) ++ rowWrites variant ⟨first + 1, by omega⟩ :=
    prefixWrites_succ variant (first + 1) (by omega)
  rw [step3, step2, step1, prefixWrites_succ variant first (by omega)]
  simp only [List.append_assoc]

private theorem loop_boundary_words (variant : Variant) (count : Nat) (bound : count ≤ 55) :
    wordRun (fun cell => (old cell).word) (prefixWrites variant (6 + 4 * count)) =
      loopWords (128 + count) (55 - count) (if count = 0 then 0 else 136) none := by
  induction count with
  | zero => exact loop_boot_words variant
  | succ count ih =>
      have small : count < 55 := by omega
      have prefixCount : 6 + 4 * (count + 1) = (6 + 4 * count) + 4 := by omega
      rw [prefixCount, prefixWrites_four variant _ (by omega), wordRun_append, ih (by omega)]
      have iteration := loop_words_iteration variant ⟨count, small⟩ (if count = 0 then 0 else 136)
      change wordRun (loopWords (128 + count) (55 - count) (if count = 0 then 0 else 136) none)
        (rowWrites variant ⟨6 + 4 * count, by omega⟩ ++
         rowWrites variant ⟨6 + 4 * count + 1, by omega⟩ ++
         rowWrites variant ⟨6 + 4 * count + 2, by omega⟩ ++
         rowWrites variant ⟨6 + 4 * count + 3, by omega⟩) =
          loopWords (128 + (count + 1)) (55 - (count + 1)) 136 none at iteration
      simpa only [show ¬count + 1 = 0 by omega, ↓reduceIte] using iteration

private def phaseWords (index : Fin 55) (phase : Fin 4) : Cell → Word :=
  match phase.val with
  | 0 => loopWords (128 + index.val) (55 - index.val) (if index.val = 0 then 0 else 136) none
  | 1 => loopWords (129 + index.val) (55 - index.val) (if index.val = 0 then 0 else 136) none
  | 2 => loopWords (129 + index.val) (55 - index.val) 136 none
  | _ => loopWords (129 + index.val) (54 - index.val) 136 none

private theorem loop_phase_words (variant : Variant) (index : Fin 55) (phase : Fin 4) :
    wordRun (fun cell => (old cell).word) (prefixWrites variant (gapRow index phase).val) =
      phaseWords index phase := by
  have small := index.isLt
  have boundary := loop_boundary_words variant index.val (by omega)
  fin_cases phase
  · exact boundary
  · change wordRun _ (prefixWrites variant ((6 + 4 * index.val) + 1)) = _
    rw [prefix_words_succ variant _ (by omega), boundary]
    exact loop_row_zero variant index _ _
  · change wordRun _ (prefixWrites variant (((6 + 4 * index.val) + 1) + 1)) = _
    rw [prefix_words_succ variant _ (by omega), prefix_words_succ variant _ (by omega), boundary]
    change wordRun (wordRun
      (loopWords (128 + index.val) (55 - index.val) (if index.val = 0 then 0 else 136) none)
      (rowWrites variant (gapRow index 0))) (rowWrites variant (gapRow index 1)) = _
    rw [loop_row_zero]
    exact loop_row_jal variant index _
  · change wordRun _ (prefixWrites variant ((((6 + 4 * index.val) + 1) + 1) + 1)) = _
    rw [prefix_words_succ variant _ (by omega), prefix_words_succ variant _ (by omega),
      prefix_words_succ variant _ (by omega), boundary]
    change wordRun (wordRun (wordRun
      (loopWords (128 + index.val) (55 - index.val) (if index.val = 0 then 0 else 136) none)
      (rowWrites variant (gapRow index 0))) (rowWrites variant (gapRow index 1)))
      (rowWrites variant (gapRow index 2)) = _
    rw [loop_row_zero, loop_row_jal]
    exact loop_row_decrement variant index

private def storedAddress : Variant → Option (BitVec 32)
  | .baseline => none
  | .scratch => some scratchAddress
  | .protectedMessage => some messageAddress

private theorem loopWords_store (control counter link : Nat) (address : BitVec 32) :
    Function.update (loopWords control counter link none) (.ram address) (wordOfNat 7) =
      loopWords control counter link (some address) := by
  funext cell
  cases cell <;> simp [Function.update, loopWords, eq_comm]

private theorem store_gap_words (variant : Variant) :
    wordRun (loopWords 183 0 136 none) (rowWrites variant 226) =
      loopWords 183 0 136 (storedAddress variant) := by
  cases variant
  · have writes : rowWrites .baseline 226 =
        [⟨.register 2, 908, wordOfNat 7⟩, ⟨.register 0, 909, wordOfNat 0⟩,
         ⟨.register 2, 910, wordOfNat 7⟩] := by rfl
    rw [writes]
    apply wordRun_refreshes
    intro write member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl
  · have writes : rowWrites .scratch 226 =
        [⟨.register 10, 908, Word.ofBitVec stateAddress⟩, ⟨.register 2, 909, wordOfNat 7⟩,
         ⟨.ram scratchAddress, 910, wordOfNat 7⟩] := by rfl
    rw [writes]
    rw [wordRun_cpu_three _ _ _ _ (by rfl) (by rfl)]
    exact loopWords_store _ _ _ _
  · have writes : rowWrites .protectedMessage 226 =
        [⟨.register 11, 908, Word.ofBitVec messageAddress⟩, ⟨.register 2, 909, wordOfNat 7⟩,
         ⟨.ram messageAddress, 910, wordOfNat 7⟩] := by rfl
    rw [writes]
    rw [wordRun_cpu_three _ _ _ _ (by rfl) (by rfl)]
    exact loopWords_store _ _ _ _

private theorem final_worker_words (variant : Variant) :
    wordRun (loopWords 183 0 136 (storedAddress variant)) (workerWrites 55) =
      loopWords 128 0 136 (storedAddress variant) := by
  let start := loopWords 183 0 136 (storedAddress variant)
  let makeWrite (port : Fin 9) : Write :=
    ⟨(workerCells 55)[port], callStart 55 + 3, workerValue 55 port⟩
  have refreshes : ∀ port : Fin 8, start (makeWrite port.castSucc).cell = (makeWrite port.castSucc).value := by
    intro port
    fin_cases port <;> cases variant
    all_goals simp [start, makeWrite, workerCells, workerValue, loopWords, storedAddress,
      Blake2G.Control.step, Blake2G.controllerAt, Blake2G.controlAt, Blake2G.callCount,
      Blake2G.Control.stateLanes, Blake2G.Control.messageSchedule,
      stateAddress, messageAddress, scratchAddress]
  have unchanged : wordRun start ((List.finRange 8).map fun port => makeWrite port.castSucc) = start := by
    apply wordRun_refreshes
    intro write member
    obtain ⟨port, _, rfl⟩ := List.mem_map.mp member
    exact refreshes port
  have cell : (makeWrite 8).cell = .register 12 := rfl
  have value : (makeWrite 8).value = wordOfNat 128 := by
    change (Blake2G.Control.step (Blake2G.controllerAt true 55)).register = wordOfNat 128
    decide +kernel
  change wordRun start ((List.finRange 9).map makeWrite) = _
  rw [List.finRange_succ_last, List.map_append, List.map_map, wordRun_append]
  change wordRun
    (wordRun start ((List.finRange 8).map fun port => makeWrite port.castSucc)) [makeWrite 8] = _
  rw [unchanged]
  change Function.update start (makeWrite 8).cell (makeWrite 8).value = _
  rw [cell, value]
  exact loopWords_control _ _ _ _ _

private theorem final_row_words (variant : Variant) :
    wordRun (loopWords 183 0 136 (storedAddress variant)) (rowWrites variant 227) =
      loopWords 128 0 136 (storedAddress variant) := by
  rw [rowWrites]
  simp only [show ¬((227 : Fin 228).val < 226 ∧ ((227 : Fin 228).val - 6) % 4 = 0 ∧
    6 ≤ (227 : Fin 228).val) by decide, ↓reduceDIte, wordRun_append]
  have unchanged : wordRun (loopWords 183 0 136 (storedAddress variant)) (machineWrites variant 227) =
      loopWords 183 0 136 (storedAddress variant) := by
    have writes : machineWrites variant 227 =
        [⟨.register 0, 912, wordOfNat 0⟩, ⟨.register 0, 914, wordOfNat 0⟩] := by rfl
    rw [writes]
    apply wordRun_refreshes
    intro write member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl
  rw [unchanged]
  exact final_worker_words variant

private theorem terminal_words (variant : Variant) :
    (fun cell => (final variant cell).word) = loopWords 128 0 136 (storedAddress variant) := by
  rw [← ledger_final, ledger_word_run]
  have boundary := loop_boundary_words variant 55 (by decide)
  change wordRun _ (prefixWrites variant (227 + 1)) = _
  rw [prefix_words_succ variant 227 (by decide), prefix_words_succ variant 226 (by decide)]
  change wordRun (wordRun (wordRun _ (prefixWrites variant (6 + 4 * 55)))
    (rowWrites variant 226)) (rowWrites variant 227) = _
  rw [boundary]
  change wordRun (wordRun (loopWords 183 0 136 none) (rowWrites variant 226))
    (rowWrites variant 227) = _
  rw [store_gap_words, final_row_words]


/- Actual cell-domain, predecessor-clock and imported value/time projections.
   These identities are support for native ledger matching, not new caller premises. -/

private theorem register_mem_cells (register : BitVec 5) : Cell.register register ∈ cells := by
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_map.mpr
  refine ⟨⟨register.toNat, register.isLt⟩, List.mem_finRange _, ?_⟩
  simp

private theorem state_mem_cells (word : Fin 16) :
    Cell.ram (stateAddress + BitVec.ofNat 32 (4 * word.val)) ∈ cells := by
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨word, List.mem_finRange _, rfl⟩

private theorem message_mem_cells (word : Fin 16) :
    Cell.ram (messageAddress + BitVec.ofNat 32 (4 * word.val)) ∈ cells := by
  apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨word, List.mem_finRange _, rfl⟩

private theorem scratch_mem_cells : Cell.ram scratchAddress ∈ cells := by
  apply List.mem_append_right
  exact List.mem_singleton_self _

private theorem store_mem_cells (variant : Variant) : Cell.ram (storeAddress variant) ∈ cells := by
  cases variant
  · simpa [storeAddress] using message_mem_cells 0
  · simpa [storeAddress] using scratch_mem_cells
  · simpa [storeAddress] using message_mem_cells 0

private theorem cells_nodup : cells.Nodup := by decide +kernel

private theorem machine_cells_mem (variant : Variant) (index : Fin 228) (port : Fin 3) :
    (machineCells variant index)[port] ∈ cells := by
  fin_cases port
  · exact register_mem_cells _
  · exact register_mem_cells _
  · change (if isStore variant index then Cell.ram (storeAddress variant)
      else Cell.register (metadata variant index).rd) ∈ cells
    split
    · exact store_mem_cells variant
    · exact register_mem_cells _

private theorem worker_cells_mem (index : Fin 56) (port : Fin 9) :
    (workerCells index)[port] ∈ cells := by
  have stateBound := Blake2G.Control.Proofs.state_offsets_bounded (Blake2G.controllerAt true index.val)
  have messageBound := Blake2G.Control.Proofs.message_offsets_bounded (Blake2G.controllerAt true index.val)
  fin_cases port
  · exact register_mem_cells _
  · exact state_mem_cells ⟨_, stateBound 0⟩
  · exact state_mem_cells ⟨_, stateBound 1⟩
  · exact state_mem_cells ⟨_, stateBound 2⟩
  · exact state_mem_cells ⟨_, stateBound 3⟩
  · exact register_mem_cells _
  · exact message_mem_cells ⟨_, messageBound 0⟩
  · exact message_mem_cells ⟨_, messageBound 1⟩
  · exact register_mem_cells _

private theorem machine_writes_mem (variant : Variant) (index : Fin 228) :
    ∀ write ∈ machineWrites variant index, write.cell ∈ cells := by
  intro write member
  dsimp only [machineWrites] at member
  split_ifs at member
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact machine_cells_mem variant index 0
    · exact machine_cells_mem variant index 2
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact machine_cells_mem variant index 0
    · exact machine_cells_mem variant index 1
    · exact machine_cells_mem variant index 2

private theorem worker_writes_mem (index : Fin 56) :
    ∀ write ∈ workerWrites index, write.cell ∈ cells := by
  intro write member
  obtain ⟨port, _, rfl⟩ := List.mem_map.mp member
  exact worker_cells_mem index port

private theorem row_writes_mem (variant : Variant) (index : Fin 228) :
    ∀ write ∈ rowWrites variant index, write.cell ∈ cells := by
  intro write member
  rw [row_ledger_writes] at member
  rcases List.mem_append.mp member with cpu | worker
  · exact machine_writes_mem variant index write cpu
  · obtain ⟨index, _, member⟩ := List.mem_flatMap.mp worker
    exact worker_writes_mem index write member

private theorem prefix_writes_mem (variant : Variant) (count : Nat) :
    ∀ write ∈ prefixWrites variant count, write.cell ∈ cells := by
  intro write member
  unfold prefixWrites at member
  obtain ⟨index, _, member⟩ := List.mem_flatMap.mp member
  split_ifs at member
  · exact row_writes_mem variant _ write member
  · cases member

private theorem ledger_address_invariant (writes : List Write)
    (start : Cell → MemoryToken babyBearModulus)
    (initial : ∀ cell, (start cell).address = cell.addressCode) :
    ∀ cell, (ledgerRun start writes cell).address = cell.addressCode := by
  induction writes generalizing start with
  | nil => exact initial
  | cons write rest ih =>
      change ∀ cell, (ledgerRun (ledgerPut start write) rest cell).address = cell.addressCode
      apply ih
      intro cell
      by_cases equal : cell = write.cell
      · subst cell; simp only [ledgerPut, Function.update_self, writeTokenOf]
      · simpa only [ledgerPut, Function.update_of_ne equal] using initial cell

private theorem ledger_stamps_cast (writes : List Write) (cell : Cell) (stamp : Nat) :
    writes.foldl
      (fun time write => if write.cell = cell then ((write.stamp : ZMod babyBearModulus), (0 : ZMod babyBearModulus)) else time)
      ((stamp : ZMod babyBearModulus), (0 : ZMod babyBearModulus)) =
    (((writes.foldl (fun time write => if write.cell = cell then write.stamp else time) stamp : Nat) :
      ZMod babyBearModulus), (0 : ZMod babyBearModulus)) := by
  induction writes generalizing stamp with
  | nil => rfl
  | cons write rest ih =>
      simp only [List.foldl_cons]
      by_cases equal : write.cell = cell
      · simp only [if_pos equal]; exact ih write.stamp
      · simp only [if_neg equal]; exact ih stamp

private theorem ledger_previous_stamp (writes : List Write) (cell : Cell) :
    (ledgerRun old writes cell).time = ((lastStamp writes cell : Nat), 0) := by
  rw [ledger_time_run]
  simpa only [old, Cell.initialToken, lastStamp, Nat.cast_zero] using ledger_stamps_cast writes cell 0

private theorem token_eq_of_word {left right : MemoryToken babyBearModulus}
    (address : left.address = right.address) (time : left.time = right.time)
    (word : left.word = right.word) : left = right := by
  have encoded : left.value = right.value := by
    have pair := congrArg (fun value : Word => Nat.pair value.lo value.hi) word
    simpa only [MemoryToken.word, Nat.pair_unpair] using pair
  cases left
  cases right
  cases address
  cases time
  cases encoded
  rfl

/-- Exact full-domain balance for the actual candidate chronological writes.
This theorem is algebra only. Native read/write IDENTITIES are still needed
before it can establish MixedMemoryAccepted.memory. -/
private theorem chronological_balance (variant : Variant) :
    (cells.map old ++ (prefixWrites variant 228).map writeTokenOf).Perm
      (cells.map (final variant) ++ ledgerReads old (prefixWrites variant 228)) := by
  have balance := ledger_balance cells cells_nodup (prefixWrites variant 228)
    (prefix_writes_mem variant 228) old
  rw [ledger_final] at balance
  exact balance

private theorem last_stamp_limit (writes : List Write) (cell : Cell) (stamp limit : Nat)
    (small : stamp < limit) (bounds : ∀ write ∈ writes, write.stamp < limit) :
    writes.foldl (fun value write => if write.cell = cell then write.stamp else value) stamp < limit := by
  induction writes generalizing stamp with
  | nil => exact small
  | cons write rest ih =>
      apply ih
      · dsimp only
        split_ifs
        · exact bounds write (by simp)
        · exact small
      · intro item member; exact bounds item (by simp [member])

private theorem native_active_call_row (index : Fin 228)
    (active : index.val < 226 ∧ (index.val - 6) % 4 = 0 ∧ 6 ≤ index.val) :
    callRow ⟨iteration index, by dsimp [iteration]; have := index.isLt; omega⟩ = index := by
  apply Fin.ext
  have inside : iteration index < 55 := by dsimp [iteration]; omega
  change (if iteration index < 55 then 6 + 4 * iteration index else 227) = index.val
  rw [if_pos inside]
  dsimp only [iteration]
  omega

private theorem machine_write_before_worker (variant : Variant) (index : Fin 228)
    {write : Write} (member : write ∈ machineWrites variant index) :
    write.stamp < machineClock index + 3 := by
  dsimp only [machineWrites] at member
  split_ifs at member
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> dsimp only <;> omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> dsimp only <;> omega

private theorem row_write_before_end (variant : Variant) (index : Fin 228)
    {write : Write} (member : write ∈ rowWrites variant index) :
    write.stamp < machineClock index + 4 := by
  rw [row_ledger_writes] at member
  rcases List.mem_append.mp member with machine | worker
  · exact Nat.lt_trans (machine_write_before_worker variant index machine) (by omega)
  · obtain ⟨workerIndex, workerMember, member⟩ := List.mem_flatMap.mp worker
    obtain ⟨port, _, rfl⟩ := List.mem_map.mp member
    change callStart workerIndex + 3 < machineClock index + 4
    dsimp only [rowWorkers] at workerMember
    split_ifs at workerMember with active last
    · have same := List.mem_singleton.mp workerMember
      subst workerIndex
      unfold callStart
      rw [native_active_call_row index active]
      dsimp only [machineClock]
      omega
    · have same := List.mem_singleton.mp workerMember
      subst workerIndex
      have sameIndex : index = (227 : Fin 228) := Fin.ext last
      subst index
      decide
    · cases workerMember

private theorem prefix_write_before_cut (variant : Variant) (count : Nat)
    {write : Write} (member : write ∈ prefixWrites variant count) : write.stamp < 4 + 4 * count := by
  unfold prefixWrites at member
  obtain ⟨index, _, member⟩ := List.mem_flatMap.mp member
  split_ifs at member with bound
  · have current := row_write_before_end variant ⟨index.val, bound⟩ member
    dsimp only [machineClock] at current
    have past := index.isLt
    omega
  · cases member

theorem cpu_previous_before_current (variant : Variant) (index : Fin 228) (port : Fin 3) :
    previous variant index port < machineClock index + port.val := by
  have positive : 0 < machineClock index + port.val := by dsimp [machineClock]; omega
  unfold previous
  split_ifs
  · exact positive
  · apply last_stamp_limit _ _ 0 _ positive
    intro write member
    rcases List.mem_append.mp member with earlier | sameRow
    · have before := prefix_write_before_cut variant index.val earlier
      dsimp only [machineClock]
      omega
    · exact of_decide_eq_true (List.mem_filter.mp sameRow).2

theorem worker_previous_before_current (variant : Variant) (index : Fin 56) (port : Fin 9) :
    workerReadStamp variant index port < callStart index + 3 := by
  apply last_stamp_limit _ _ 0 _ (by dsimp [callStart]; omega)
  intro write member
  rcases List.mem_append.mp member with earlier | cpu
  · have before := prefix_write_before_cut variant (callRow index).val earlier
    dsimp only [callStart]
    omega
  · exact machine_write_before_worker variant (callRow index) cpu

private theorem native_delta_range (current previous : Nat)
    (past : previous < current) (small : current < 916) :
    (((current : ZMod babyBearModulus) - previous - 1).val < timestampBase) := by
  have old : previous ≤ current := by omega
  have remainder : 1 ≤ current - previous := by omega
  have cast : ((current - previous - 1 : Nat) : ZMod babyBearModulus) =
      (current : ZMod babyBearModulus) - previous - 1 := by
    simp only [Nat.cast_sub remainder, Nat.cast_sub old, Nat.cast_one]
  rw [← cast]
  have canonical : current - previous - 1 < babyBearModulus := by
    dsimp [babyBearModulus]; omega
  rw [ZMod.val_natCast_of_lt canonical]
  dsimp [timestampBase]
  omega

theorem current_cpu_clock_bound (index : Fin 228) (port : Fin 3) :
    machineClock index + port.val < 916 := by
  have rowBound := index.isLt
  have portBound := port.isLt
  dsimp [machineClock]
  omega

theorem current_worker_clock_bound (index : Fin 56) : callStart index + 3 < 916 := by
  have bound := (callRow index).isLt
  unfold callStart
  omega

private theorem source0_word_bound (variant : Variant) (index : Fin 228) :
    source0 variant index < 2 ^ 32 := by
  unfold source0
  split_ifs
  all_goals solve
    | (norm_num [stateAddress, messageAddress, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat])
    | omega
    | (cases variant <;> decide +kernel)

private theorem source1_word_bound (variant : Variant) (index : Fin 228) :
    source1 variant index < 2 ^ 32 := by
  unfold source1
  split_ifs <;> decide

private theorem old_destination_word_bound (variant : Variant) (index : Fin 228) :
    oldDestination variant index < 2 ^ 32 := by
  unfold oldDestination
  split_ifs <;> omega

private theorem new_destination_word_bound (variant : Variant) (index : Fin 228) :
    newDestination variant index < 2 ^ 32 := by
  unfold newDestination
  split_ifs
  all_goals solve
    | (norm_num [stateAddress, messageAddress])
    | omega

/-- Integer splitting occurs before field embedding. This identity would be
false for field division in the high limb, even when native clocks are tiny. -/
private theorem native_nat_word (value : Nat) (bound : value < 2 ^ 32) :
    (⟨(((value % 65536 : Nat) : ZMod babyBearModulus)).val,
      (((value / 65536 : Nat) : ZMod babyBearModulus)).val⟩ : Word) = wordOfNat value := by
  have low : value % 65536 < babyBearModulus := by
    have := Nat.mod_lt value (by decide : 0 < 65536)
    dsimp [babyBearModulus]; omega
  have highSmall : value / 65536 < 65536 := by omega
  have high : value / 65536 < babyBearModulus := by dsimp [babyBearModulus]; omega
  simp only [wordOfNat, Word.ofBitVec, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound,
    limbBase, ZMod.val_natCast_of_lt low, ZMod.val_natCast_of_lt high]

private def cpuReadWord (variant : Variant) (index : Fin 228) (port : Fin 3) : Word :=
  if port.val = 0 then wordOfNat (source0 variant index)
  else if port.val = 1 then wordOfNat (source1 variant index)
  else wordOfNat (oldDestination variant index)

private def cpuWrittenWord (variant : Variant) (index : Fin 228) (port : Fin 3) : Word :=
  if port.val = 0 then wordOfNat (source0 variant index)
  else if port.val = 1 then wordOfNat (source1 variant index)
  else wordOfNat (newDestination variant index)

/-- Actual native read-value projections, including the old destination value.
The virtual CSR slot is later excluded by the actual caller selector. -/
private theorem cpu_native_read_words (variant : Variant) (index : Fin 228) (port : Fin 3) :
    (readToken (machineAssignment variant index) UnifiedReduced.importedConstraintsMemoryPorts[port]).word =
      cpuReadWord variant index port := by
  fin_cases port
  all_goals simp only [UnifiedReduced.importedConstraintsMemoryPorts, readToken, MemoryPort.readCode,
    WordColumns.code, WordColumns.evaluate, MemoryToken.word, Nat.unpair_pair,
    cpuReadWord, machineAssignment]
  · exact native_nat_word _ (source0_word_bound variant index)
  · exact native_nat_word _ (source1_word_bound variant index)
  · exact native_nat_word _ (old_destination_word_bound variant index)

/-- Actual native write-value projections. Readonly source ports refresh the
same raw word and the destination port retains its real write columns. -/
private theorem cpu_native_written_words (variant : Variant) (index : Fin 228) (port : Fin 3) :
    (writeToken UnifiedReduced.importedConstraintsTraceColumns (machineAssignment variant index)
      UnifiedReduced.importedConstraintsMemoryPorts[port]).word = cpuWrittenWord variant index port := by
  fin_cases port
  all_goals simp only [UnifiedReduced.importedConstraintsMemoryPorts, writeToken, MemoryPort.writeCode,
    WordColumns.code, WordColumns.evaluate, MemoryToken.word, Nat.unpair_pair,
    cpuWrittenWord, machineAssignment]
  · exact native_nat_word _ (source0_word_bound variant index)
  · exact native_nat_word _ (source1_word_bound variant index)
  · exact native_nat_word _ (new_destination_word_bound variant index)

private theorem cpu_native_read_clocks (variant : Variant) (index : Fin 228) (port : Fin 3) :
    (readToken (machineAssignment variant index) UnifiedReduced.importedConstraintsMemoryPorts[port]).time =
      ((previous variant index port : Nat), 0) := by
  fin_cases port
  all_goals simp [UnifiedReduced.importedConstraintsMemoryPorts, readToken, rawPair, machineAssignment]

private theorem cpu_native_write_clocks (variant : Variant) (index : Fin 228) (port : Fin 3) :
    (writeToken UnifiedReduced.importedConstraintsTraceColumns (machineAssignment variant index)
      UnifiedReduced.importedConstraintsMemoryPorts[port]).time =
        ((machineClock index + port.val : Nat), 0) := by
  fin_cases port
  all_goals simp [UnifiedReduced.importedConstraintsTraceColumns, UnifiedReduced.importedConstraintsMemoryPorts,
    writeToken, rawPair, machineAssignment, Nat.cast_add]

private theorem worker_native_read_clocks (variant : Variant) (index : Fin 56) (port : Fin 9) :
    (readToken (workerAssignment variant index) Blake2G.importedConstraintsMemoryPorts[port]).time =
      ((workerReadStamp variant index port : Nat), 0) := by
  fin_cases port
  all_goals simp [Blake2G.importedConstraintsMemoryPorts, readToken, rawPair, workerAssignment]

private theorem worker_native_write_clocks (variant : Variant) (index : Fin 56) (port : Fin 9) :
    ((⟨.blakeG, workerAssignment variant index⟩ : Delegation.Row babyBearModulus).writeToken
      Blake2G.importedConstraintsMemoryPorts[port]).time = ((callStart index + 3 : Nat), 0) := by
  fin_cases port
  all_goals simp [Blake2G.importedConstraintsDelegationColumns, Blake2G.importedConstraintsMemoryPorts,
    Delegation.Row.writeToken, Delegation.Row.columns, rawPair, workerAssignment, Nat.cast_add,
    add_assoc]
  all_goals norm_num


/- Atomic ledger serialization and exact imported physical address projections.
   Matching still requires the concrete predecessor-value and raw-token identities. -/

private def ledgerSteps (start : Cell → MemoryToken babyBearModulus) :
    List Write → List (MemoryToken babyBearModulus × MemoryToken babyBearModulus)
  | [] => []
  | write :: rest =>
      (start write.cell, writeTokenOf write) :: ledgerSteps (ledgerPut start write) rest

private theorem ledgerSteps_append (start : Cell → MemoryToken babyBearModulus)
    (first second : List Write) :
    ledgerSteps start (first ++ second) =
      ledgerSteps start first ++ ledgerSteps (ledgerRun start first) second := by
  induction first generalizing start with
  | nil => rfl
  | cons write rest ih =>
      simp only [List.cons_append, ledgerSteps, List.cons.injEq]
      exact ⟨True.intro, ih (ledgerPut start write)⟩

private theorem ledgerSteps_reads (start : Cell → MemoryToken babyBearModulus) (writes : List Write) :
    (ledgerSteps start writes).map Prod.fst = ledgerReads start writes := by
  induction writes generalizing start with
  | nil => rfl
  | cons write rest ih => simp only [ledgerSteps, List.map_cons, ledgerReads, ih]

private theorem ledgerSteps_writes (start : Cell → MemoryToken babyBearModulus) (writes : List Write) :
    (ledgerSteps start writes).map Prod.snd = writes.map writeTokenOf := by
  induction writes generalizing start with
  | nil => rfl
  | cons write rest ih => simp only [ledgerSteps, List.map_cons, ih]

private theorem ledgerPut_frame (start : Cell → MemoryToken babyBearModulus)
    (writes : List Write) (cell : Cell) (outside : ∀ write ∈ writes, write.cell ≠ cell) :
    ledgerRun start writes cell = start cell := by
  induction writes generalizing start with
  | nil => rfl
  | cons write rest ih =>
      change ledgerRun (ledgerPut start write) rest cell = _
      rw [ih (ledgerPut start write) (fun item member => outside item (by simp [member]))]
      simp only [ledgerPut, Function.update_of_ne (Ne.symm (outside write (by simp)))]

/-- Atomic native workers have one original predecessor per distinct cell,
even when all their writes share the same actual clock. Serializing their
ports therefore preserves every raw predecessor token without dropping events. -/
private theorem ledgerSteps_distinct (start : Cell → MemoryToken babyBearModulus)
    (writes : List Write) (distinct : (writes.map Write.cell).Nodup) :
    ledgerSteps start writes = writes.map (fun write => (start write.cell, writeTokenOf write)) := by
  induction writes generalizing start with
  | nil => rfl
  | cons write rest ih =>
      have facts := List.nodup_cons.mp distinct
      simp only [ledgerSteps, List.map_cons, List.cons.injEq]
      refine ⟨True.intro, (ih (ledgerPut start write) facts.2).trans ?_⟩
      apply List.map_congr_left
      intro other member
      have different : other.cell ≠ write.cell := by
        intro same
        apply facts.1
        exact List.mem_map.mpr ⟨other, member, same⟩
      simp only [ledgerPut, Function.update_of_ne different]

private theorem worker_cells_nodup (index : Fin 56) : (workerCells index).toList.Nodup := by
  fin_cases index <;> decide +kernel

private theorem worker_writes_distinct (index : Fin 56) :
    ((workerWrites index).map Write.cell).Nodup := by
  have same : (workerWrites index).map Write.cell = (workerCells index).toList := by
    simp only [workerWrites, List.map_map, Function.comp_def]
    apply List.ext_getElem
    · simp
    · intro position left right; simp
  rw [same]
  exact worker_cells_nodup index

private theorem worker_ledger_atomic (variant : Variant) (index : Fin 56) :
    ledgerSteps (ledgerRun old
      (prefixWrites variant (callRow index).val ++ machineWrites variant (callRow index)))
      (workerWrites index) =
    (workerWrites index).map fun write =>
      (ledgerRun old (prefixWrites variant (callRow index).val ++ machineWrites variant (callRow index)) write.cell,
        writeTokenOf write) := by
  exact ledgerSteps_distinct _ _ (worker_writes_distinct index)

private theorem store_occurrence (index : Fin 228) :
    (rowCodeIndex index).val = 10 ↔ index.val = 226 := by
  have bound := index.isLt
  have remainder := Nat.mod_lt (index.val - 6) (by decide : 0 < 4)
  dsimp only [rowCodeIndex]
  split_ifs <;> omega

private theorem metadata_selectors (variant : Variant) (index : Fin 228) :
    (metadata variant index).mask.testBit 17 = false ∧
      (metadata variant index).mask.testBit 18 = isStore variant index ∧
      (metadata variant index).mask.testBit 7 = isCaller index := by
  have occurrence := store_occurrence index
  generalize code : rowCodeIndex index = entry at occurrence
  fin_cases entry <;> cases variant
  all_goals simp_all [metadata, isStore, isCaller, codeEntry, Tests.DelegationCaller.entry,
    UnifiedReduced.decoderFields, DecoderData.mapFamily]
  all_goals decide +kernel

theorem native_selected_iff (variant : Variant) (index : Fin 228) :
    UnifiedReduced.Caller.Selected (machineAssignment variant index) ↔ isCaller index = true := by
  have caller := (metadata_selectors variant index).2.2
  simp only [UnifiedReduced.Caller.Selected, UnifiedReduced.importedConstraintsDecoderColumns]
  simp [machineAssignment, caller]

private theorem register_field_bound (register : BitVec 5) : register.toNat < babyBearModulus := by
  have bound := register.isLt
  dsimp [babyBearModulus]
  omega

private theorem field_ram_address (low high : Nat) (lowBound : low < 65536) (highBound : high < 65536) :
    Nat.pair 1 (Nat.pair ((low : ZMod babyBearModulus)).val ((high : ZMod babyBearModulus)).val) =
      (Cell.ram (BitVec.ofNat 32 (low + 65536 * high))).addressCode := by
  have lowField : low < babyBearModulus := by dsimp [babyBearModulus]; omega
  have highField : high < babyBearModulus := by dsimp [babyBearModulus]; omega
  have whole : low + 65536 * high < 2 ^ 32 := by omega
  have lo : (low + 65536 * high) % 65536 = low := by omega
  have hi : (low + 65536 * high) / 65536 = high := by omega
  simp only [ZMod.val_natCast_of_lt lowField, ZMod.val_natCast_of_lt highField,
    Cell.addressCode, Word.ofBitVec, BitVec.toNat_ofNat, Nat.mod_eq_of_lt whole,
    limbBase, lo, hi]

private theorem cpu_native_address (variant : Variant) (index : Fin 228) (port : Fin 3)
    (physical : port.val ≠ 1 ∨ isCaller index = false) :
    UnifiedReduced.importedConstraintsMemoryPorts[port].address.code (machineAssignment variant index) =
      ((machineCells variant index)[port]).addressCode := by
  have selectors := metadata_selectors variant index
  have rs1 := register_field_bound (metadata variant index).rs1
  have rs2 := register_field_bound (metadata variant index).rs2
  have rd := register_field_bound (metadata variant index).rd
  fin_cases port
  · simp [UnifiedReduced.importedConstraintsMemoryPorts, MemoryAddress.code,
      machineAssignment, machineCells, Cell.addressCode, Nat.mod_eq_of_lt rs1]
  · have ordinary : isCaller index = false := physical.resolve_left (by simp)
    simp [UnifiedReduced.importedConstraintsMemoryPorts, MemoryAddress.code, pairCode,
      machineAssignment, machineCells, selectors.1, ordinary, Cell.addressCode,
      ZMod.val_natCast_of_lt rs2]
  · have addressBound := Word.ofBitVec_bound (storeAddress variant)
    have low : (Word.ofBitVec (storeAddress variant)).lo < babyBearModulus :=
      Nat.lt_trans addressBound.1 (by decide)
    have high : (Word.ofBitVec (storeAddress variant)).hi < babyBearModulus :=
      Nat.lt_trans addressBound.2 (by decide)
    cases store : isStore variant index
    · simp [UnifiedReduced.importedConstraintsMemoryPorts, MemoryAddress.code, pairCode,
        machineAssignment, machineCells, selectors.2.1, store, Cell.addressCode,
        ZMod.val_natCast_of_lt rd]
    · simp [UnifiedReduced.importedConstraintsMemoryPorts, MemoryAddress.code, pairCode,
        machineAssignment, machineCells, selectors.2.1, store, Cell.addressCode,
        ZMod.val_natCast_of_lt low, ZMod.val_natCast_of_lt high]
      decide +kernel

private theorem worker_state_address (offset : Nat) (bound : offset < 16) :
    Nat.pair 1 (Nat.pair (((4 * offset : Nat) : ZMod babyBearModulus)).val (512 : ZMod babyBearModulus).val) =
      (Cell.ram (stateAddress + BitVec.ofNat 32 (4 * offset))).addressCode := by
  have address : BitVec.ofNat 32 (4 * offset + 65536 * 512) =
      stateAddress + BitVec.ofNat 32 (4 * offset) := by
    apply BitVec.eq_of_toNat_eq
    simp [stateAddress, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [← address]
  exact field_ram_address _ _ (by omega) (by decide)

private theorem worker_message_address (offset : Nat) (bound : offset < 16) :
    Nat.pair 1 (Nat.pair (((64 + 4 * offset : Nat) : ZMod babyBearModulus)).val (512 : ZMod babyBearModulus).val) =
      (Cell.ram (messageAddress + BitVec.ofNat 32 (4 * offset))).addressCode := by
  have address : BitVec.ofNat 32 (64 + 4 * offset + 65536 * 512) =
      messageAddress + BitVec.ofNat 32 (4 * offset) := by
    apply BitVec.eq_of_toNat_eq
    simp [messageAddress, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [← address]
  exact field_ram_address _ _ (by omega) (by decide)

private theorem worker_native_address (variant : Variant) (index : Fin 56) (port : Fin 9) :
    Blake2G.importedConstraintsMemoryPorts[port].address.code (workerAssignment variant index) =
      ((workerCells index)[port]).addressCode := by
  have stateBound := Blake2G.Control.Proofs.state_offsets_bounded (Blake2G.controllerAt true index.val)
  have messageBound := Blake2G.Control.Proofs.message_offsets_bounded (Blake2G.controllerAt true index.val)
  let control := Blake2G.Control.step (Blake2G.controllerAt true index.val)
  fin_cases port
  · rfl
  · change Nat.pair 1 (Nat.pair
      ((0 + (4 : ZMod babyBearModulus) * (control.stateOffsets[0] : Nat) + 0).val)
      (512 : ZMod babyBearModulus).val) =
        (Cell.ram (stateAddress + BitVec.ofNat 32 (4 * control.stateOffsets[0]))).addressCode
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_zero, zero_add, add_zero] using
      worker_state_address (control.stateOffsets[0]) (stateBound ⟨0, by decide⟩)
  · change Nat.pair 1 (Nat.pair
      ((0 + (4 : ZMod babyBearModulus) * (control.stateOffsets[1] : Nat) + 0).val)
      (512 : ZMod babyBearModulus).val) =
        (Cell.ram (stateAddress + BitVec.ofNat 32 (4 * control.stateOffsets[1]))).addressCode
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_zero, zero_add, add_zero] using
      worker_state_address (control.stateOffsets[1]) (stateBound ⟨1, by decide⟩)
  · change Nat.pair 1 (Nat.pair
      ((0 + (4 : ZMod babyBearModulus) * (control.stateOffsets[2] : Nat) + 0).val)
      (512 : ZMod babyBearModulus).val) =
        (Cell.ram (stateAddress + BitVec.ofNat 32 (4 * control.stateOffsets[2]))).addressCode
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_zero, zero_add, add_zero] using
      worker_state_address (control.stateOffsets[2]) (stateBound ⟨2, by decide⟩)
  · change Nat.pair 1 (Nat.pair
      ((0 + (4 : ZMod babyBearModulus) * (control.stateOffsets[3] : Nat) + 0).val)
      (512 : ZMod babyBearModulus).val) =
        (Cell.ram (stateAddress + BitVec.ofNat 32 (4 * control.stateOffsets[3]))).addressCode
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_zero, zero_add, add_zero] using
      worker_state_address (control.stateOffsets[3]) (stateBound ⟨3, by decide⟩)
  · rfl
  · change Nat.pair 1 (Nat.pair
      (((64 : ZMod babyBearModulus) + 4 * (control.messageOffsets[0] : Nat) + 0).val)
      (512 : ZMod babyBearModulus).val) =
        (Cell.ram (messageAddress + BitVec.ofNat 32 (4 * control.messageOffsets[0]))).addressCode
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, add_zero] using
      worker_message_address (control.messageOffsets[0]) (messageBound ⟨0, by decide⟩)
  · change Nat.pair 1 (Nat.pair
      (((64 : ZMod babyBearModulus) + 4 * (control.messageOffsets[1] : Nat) + 0).val)
      (512 : ZMod babyBearModulus).val) =
        (Cell.ram (messageAddress + BitVec.ofNat 32 (4 * control.messageOffsets[1]))).addressCode
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, add_zero] using
      worker_message_address (control.messageOffsets[1]) (messageBound ⟨1, by decide⟩)
  · rfl

/- Prepared closed fixture predecessor-value proofs. These are goals proved
from chronological writes, not desired-read assumptions added to an interface. -/

private theorem loop_machine_predecessor (variant : Variant) (index : Fin 55)
    (phase : Fin 4) (port : Fin 3) :
    phaseWords index phase ((machineCells variant (gapRow index phase))[port]) =
      cpuReadWord variant (gapRow index phase) port := by
  have cells : machineCells variant (gapRow index phase) =
      (match phase.val with
       | 0 => #v[.register 0, .register 0, .register 0]
       | 1 => #v[.register 0, .register 0, .register 1]
       | 2 => #v[.register 5, .register 0, .register 5]
       | _ => #v[.register 5, .register 0, .register 0]) := by
    fin_cases phase
    · change machineCells variant (gapRow index 0) = #v[.register 0, .register 0, .register 0]
      simp [machineCells, metadata, gap_caller, gap_not_store, Tests.DelegationCaller.entry,
        DecoderData.mapFamily]
    · change machineCells variant (gapRow index 1) = #v[.register 0, .register 0, .register 1]
      have code : rowCodeIndex (gapRow index 1) = 7 := loop_row_index index 1
      simp [machineCells, metadata, gap_caller, gap_not_store]
      simp only [code]
      exact ⟨rfl, rfl, rfl⟩
    · change machineCells variant (gapRow index 2) = #v[.register 5, .register 0, .register 5]
      have code : rowCodeIndex (gapRow index 2) = 8 := loop_row_index index 2
      simp [machineCells, metadata, gap_caller, gap_not_store]
      simp only [code]
      exact ⟨rfl, rfl, rfl⟩
    · change machineCells variant (gapRow index 3) = #v[.register 5, .register 0, .register 0]
      have code : rowCodeIndex (gapRow index 3) = 9 := loop_row_index index 3
      simp [machineCells, metadata, gap_caller, gap_not_store]
      simp only [code]
      exact ⟨rfl, rfl, rfl⟩
  rw [cells]
  have lower : ¬(gapRow index phase).val < 6 := by dsimp [gapRow]; omega
  have upper : (gapRow index phase).val < 226 := by
    have := index.isLt; have := phase.isLt; dsimp [gapRow]; omega
  have notOne : (gapRow index phase).val ≠ 1 := by dsimp [gapRow]; omega
  have counter : iteration (gapRow index phase) = index.val := by
    have := phase.isLt; dsimp [iteration, gapRow]; omega
  have remainder : ((gapRow index phase).val - 6) % 4 = phase.val := by
    have := phase.isLt; dsimp [gapRow]; omega
  simp only [cpuReadWord, source0, source1, oldDestination, lower, upper, notOne,
    counter, remainder, gap_not_store, Bool.false_eq_true, ↓reduceIte]
  fin_cases phase <;> fin_cases port
  all_goals simp [phaseWords, loopWords, wordOfNat, Word.ofBitVec]

private theorem machine_predecessor_words (variant : Variant) (index : Fin 228) (port : Fin 3) :
    wordRun (fun cell => (old cell).word) (prefixWrites variant index.val)
      ((machineCells variant index)[port]) = cpuReadWord variant index port := by
  by_cases early : index.val < 6
  · have boot (row : Fin 6) (selected : Fin 3) :
        wordRun (fun cell => (old cell).word) (prefixWrites variant row.val)
          ((machineCells variant ⟨row.val, by have := row.isLt; omega⟩)[selected]) =
            cpuReadWord variant ⟨row.val, by have := row.isLt; omega⟩ selected := by
      fin_cases row <;> fin_cases selected <;> cases variant
      all_goals (simp only [old, Cell.initialToken, MemoryToken.word, Nat.unpair_pair]; rfl)
    exact boot ⟨index.val, early⟩ port
  · by_cases inside : index.val < 226
    · let iterationIndex : Fin 55 := ⟨(index.val - 6) / 4, by omega⟩
      let phase : Fin 4 := ⟨(index.val - 6) % 4, Nat.mod_lt _ (by decide)⟩
      have same : index = gapRow iterationIndex phase := by
        apply Fin.ext
        dsimp [gapRow, iterationIndex, phase]
        omega
      rw [same, loop_phase_words]
      exact loop_machine_predecessor variant iterationIndex phase port
    · have last : index.val = 226 ∨ index.val = 227 := by have := index.isLt; omega
      rcases last with last | last
      · have same : index = (226 : Fin 228) := Fin.ext last
        subst index
        have boundary := loop_boundary_words variant 55 (by decide)
        rw [show (226 : Fin 228).val = 6 + 4 * 55 by decide, boundary]
        fin_cases port <;> cases variant <;> decide +kernel
      · have same : index = (227 : Fin 228) := Fin.ext last
        subst index
        have boundary := loop_boundary_words variant 55 (by decide)
        rw [show (227 : Fin 228).val = 226 + 1 by decide, prefix_words_succ variant 226 (by decide)]
        change wordRun (wordRun _ (prefixWrites variant (6 + 4 * 55))) (rowWrites variant 226) _ = _
        rw [boundary]
        change wordRun (loopWords 183 0 136 none) (rowWrites variant 226) _ = _
        rw [store_gap_words]
        fin_cases port <;> cases variant <;> decide +kernel

private def workerReadWord (index : Fin 56) (port : Fin 9) : Word :=
  if port.val = 0 then Word.ofBitVec stateAddress
  else if port.val = 5 then Word.ofBitVec messageAddress
  else if port.val = 8 then Blake2G.controlAt true index.val else ⟨0, 0⟩

private theorem worker_predecessor_words (variant : Variant) (index : Fin 56) (port : Fin 9) :
    wordRun (fun cell => (old cell).word)
      (prefixWrites variant (callRow index).val ++ machineWrites variant (callRow index))
      ((workerCells index)[port]) = workerReadWord index port := by
  rw [wordRun_append]
  by_cases ordinary : index.val < 55
  · let loopIndex : Fin 55 := ⟨index.val, ordinary⟩
    have sameRow : callRow index = gapRow loopIndex 0 := by
      apply Fin.ext
      simp [callRow, gapRow, loopIndex, ordinary]
    rw [sameRow, loop_phase_words]
    change wordRun (loopWords (128 + index.val) (55 - index.val)
      (if index.val = 0 then 0 else 136) none) (machineWrites variant (gapRow loopIndex 0)) _ = _
    have unchanged : wordRun (loopWords (128 + index.val) (55 - index.val)
        (if index.val = 0 then 0 else 136) none) (machineWrites variant (gapRow loopIndex 0)) =
        loopWords (128 + index.val) (55 - index.val) (if index.val = 0 then 0 else 136) none := by
      have first : source0 variant (gapRow loopIndex 0) = 0 := by
        dsimp [source0, gapRow, iteration]; split_ifs <;> omega
      have last : newDestination variant (gapRow loopIndex 0) = 0 := by
        dsimp [newDestination, gapRow, iteration]; split_ifs <;> omega
      have cells : machineCells variant (gapRow loopIndex 0) =
          #v[.register 0, .register 0, .register 0] := by
        simp [machineCells, metadata, gap_caller, gap_not_store, Tests.DelegationCaller.entry,
          DecoderData.mapFamily]
      apply wordRun_refreshes
      intro write member
      simp only [machineWrites, cells, gap_caller, first, last] at member
      rcases List.mem_cons.mp member with rfl | remaining
      · rfl
      · rcases List.mem_singleton.mp remaining with rfl
        rfl
    rw [unchanged]
    have bounded : 128 + index.val < 65536 := by have := index.isLt; omega
    have canonical := wordOfNat_small bounded
    fin_cases port
    all_goals simp [workerCells, workerReadWord, loopWords, Blake2G.controlAt,
      Blake2G.callCount, Nat.mod_eq_of_lt index.isLt, canonical]
  · have last : index = (55 : Fin 56) := by apply Fin.ext; have := index.isLt; omega
    subst index
    have boundary := loop_boundary_words variant 55 (by decide)
    change wordRun (wordRun _ (prefixWrites variant (226 + 1))) (machineWrites variant 227) _ = _
    rw [prefix_words_succ variant 226 (by decide)]
    change wordRun (wordRun (wordRun _ (prefixWrites variant (6 + 4 * 55)))
      (rowWrites variant 226)) (machineWrites variant 227) _ = _
    rw [boundary]
    change wordRun (wordRun (loopWords 183 0 136 none) (rowWrites variant 226))
      (machineWrites variant 227) _ = _
    rw [store_gap_words]
    have unchanged : wordRun (loopWords 183 0 136 (storedAddress variant))
        (machineWrites variant 227) = loopWords 183 0 136 (storedAddress variant) := by
      have writes : machineWrites variant 227 =
          [⟨.register 0, 912, wordOfNat 0⟩, ⟨.register 0, 914, wordOfNat 0⟩] := by rfl
      rw [writes]
      apply wordRun_refreshes
      intro write member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> rfl
    rw [unchanged]
    fin_cases port <;> cases variant
    all_goals simp [workerCells, workerReadWord, loopWords, storedAddress, wordOfNat,
      Blake2G.Control.step, Blake2G.controllerAt, Blake2G.controlAt, Blake2G.callCount,
      Blake2G.Control.stateLanes, Blake2G.Control.messageSchedule,
      stateAddress, messageAddress, scratchAddress]
    all_goals rfl

/- Actual worker read/write transfers follow from the native assignment and
the closed fixture identities below. -/

private theorem worker_native_read_words (variant : Variant) (index : Fin 56) (port : Fin 9) :
    (readToken (workerAssignment variant index) Blake2G.importedConstraintsMemoryPorts[port]).word =
      workerReadWord index port := by
  fin_cases port
  case «8» =>
    change (readToken (workerAssignment variant index) Blake2G.importedConstraintsMemoryPorts[8]).word =
      Blake2G.controlAt true index.val
    exact (worker_control variant index).1
  all_goals simp [Blake2G.importedConstraintsMemoryPorts, readToken, MemoryPort.readCode,
    WordColumns.code, WordColumns.evaluate, MemoryToken.word,
    workerAssignment, workerReadWord, stateAddress, messageAddress] <;> rfl

private theorem worker_native_written_words (variant : Variant) (index : Fin 56) (port : Fin 9) :
    ((⟨.blakeG, workerAssignment variant index⟩ : Delegation.Row babyBearModulus).writeToken
      Blake2G.importedConstraintsMemoryPorts[port]).word = workerValue index port := by
  fin_cases port
  case «8» =>
    change ((⟨.blakeG, workerAssignment variant index⟩ : Delegation.Row babyBearModulus).writeToken
      Blake2G.importedConstraintsMemoryPorts[8]).word =
        (Blake2G.Control.step (Blake2G.controllerAt true index.val)).register
    exact (worker_control variant index).2
  all_goals simp [Blake2G.importedConstraintsMemoryPorts, Delegation.Row.writeToken,
    MemoryPort.writeCode, WordColumns.code, WordColumns.evaluate, MemoryToken.word,
    workerAssignment, workerValue, stateAddress, messageAddress] <;> rfl

private theorem worker_native_write_token (variant : Variant) (index : Fin 56) (port : Fin 9) :
    (⟨.blakeG, workerAssignment variant index⟩ : Delegation.Row babyBearModulus).writeToken
      Blake2G.importedConstraintsMemoryPorts[port] =
        writeTokenOf ⟨(workerCells index)[port], callStart index + 3, workerValue index port⟩ := by
  apply token_eq_of_word
  · exact worker_native_address variant index port
  · exact worker_native_write_clocks variant index port
  · simpa only [writeTokenOf, MemoryToken.word, Nat.unpair_pair] using
      worker_native_written_words variant index port

private theorem worker_native_read_token (variant : Variant) (index : Fin 56) (port : Fin 9) :
    readToken (workerAssignment variant index) Blake2G.importedConstraintsMemoryPorts[port] =
      ledgerRun old (prefixWrites variant (callRow index).val ++ machineWrites variant (callRow index))
        ((workerCells index)[port]) := by
  let earlierWrites := prefixWrites variant (callRow index).val ++ machineWrites variant (callRow index)
  let cell := (workerCells index)[port]
  have address := ledger_address_invariant earlierWrites old (fun _ => rfl) cell
  have time := ledger_previous_stamp earlierWrites cell
  have words := congrFun (ledger_word_run old earlierWrites) cell
  have value := words.trans (worker_predecessor_words variant index port)
  apply token_eq_of_word
  · exact (worker_native_address variant index port).trans address.symm
  · exact (worker_native_read_clocks variant index port).trans time.symm
  · exact (worker_native_read_words variant index port).trans value.symm

/-- Serialize the nine actual native transfers with their exact predecessor
clock/value tokens. Same-clock writes are serialized only after proving all
nine addressed cells distinct; no access is removed or retimestamped. -/
private theorem native_worker_ledger (variant : Variant) (index : Fin 56) :
    nativeWorkerSteps variant index =
      ledgerSteps (ledgerRun old
        (prefixWrites variant (callRow index).val ++ machineWrites variant (callRow index)))
        (workerWrites index) := by
  rw [worker_ledger_atomic]
  have ports :
      Blake2G.importedConstraintsMemoryPorts.toList.map
        (fun port => (readToken (workerAssignment variant index) port,
          (⟨.blakeG, workerAssignment variant index⟩ : Delegation.Row babyBearModulus).writeToken port)) =
      (List.finRange 9).map (fun port =>
        (readToken (workerAssignment variant index) Blake2G.importedConstraintsMemoryPorts[port],
          (⟨.blakeG, workerAssignment variant index⟩ : Delegation.Row babyBearModulus).writeToken
            Blake2G.importedConstraintsMemoryPorts[port])) := by
    apply List.ext_getElem
    · rfl
    · intro position left right
      simp only [List.getElem_map, Array.getElem_toList, List.getElem_finRange, Fin.getElem_fin,
        Fin.val_cast]
  dsimp only [nativeWorkerSteps, Delegation.Row.memorySteps, Delegation.Row.ports]
  rw [ports]
  simp only [workerWrites, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro port _
  exact Prod.ext (worker_native_read_token variant index port) (worker_native_write_token variant index port)

/- Prepared exact ACTUAL architectural CPU transfer identification. -/

private def cpuPortIndices (_variant : Variant) (index : Fin 228) : List (Fin 3) :=
  if isCaller index then [0, 2] else [0, 1, 2]

private def cpuWrite (variant : Variant) (index : Fin 228) (port : Fin 3) : Write :=
  ⟨(machineCells variant index)[port], machineClock index + port.val, cpuWrittenWord variant index port⟩

private theorem cpu_write_list (variant : Variant) (index : Fin 228) :
    machineWrites variant index = (cpuPortIndices variant index).map (cpuWrite variant index) := by
  cases caller : isCaller index <;> simp [cpuPortIndices, machineWrites, caller, cpuWrite, cpuWrittenWord, wordOfNat]

private theorem cpu_port_physical (variant : Variant) (index : Fin 228) (port : Fin 3)
    (member : port ∈ cpuPortIndices variant index) : port.val ≠ 1 ∨ isCaller index = false := by
  cases caller : isCaller index
  · exact Or.inr rfl
  · simp only [cpuPortIndices, caller, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact Or.inl (by decide)

private def cpuBefore (variant : Variant) (index : Fin 228) (port : Fin 3) : List Write :=
  (machineWrites variant index).filter fun write => decide (write.stamp < machineClock index + port.val)

private theorem cpu_before_words (variant : Variant) (index : Fin 228) (port : Fin 3) :
    wordRun (wordRun (fun cell => (old cell).word) (prefixWrites variant index.val))
      (cpuBefore variant index port) =
        wordRun (fun cell => (old cell).word) (prefixWrites variant index.val) := by
  apply wordRun_refreshes
  intro write member
  obtain ⟨member, earlier⟩ := List.mem_filter.mp member
  have earlier := of_decide_eq_true earlier
  dsimp only [machineWrites] at member
  split_ifs at member
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact machine_predecessor_words variant index 0
    · have bound := port.isLt; simp only at earlier; omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact machine_predecessor_words variant index 0
    · exact machine_predecessor_words variant index 1
    · have bound := port.isLt; simp only at earlier; omega

private theorem cpu_native_write_token (variant : Variant) (index : Fin 228) (port : Fin 3)
    (member : port ∈ cpuPortIndices variant index) :
    writeToken UnifiedReduced.importedConstraintsTraceColumns (machineAssignment variant index)
      UnifiedReduced.importedConstraintsMemoryPorts[port] = writeTokenOf (cpuWrite variant index port) := by
  apply token_eq_of_word
  · exact cpu_native_address variant index port (cpu_port_physical variant index port member)
  · exact cpu_native_write_clocks variant index port
  · simpa only [writeTokenOf, cpuWrite, MemoryToken.word, Nat.unpair_pair] using
      cpu_native_written_words variant index port

private theorem cpu_native_read_token (variant : Variant) (index : Fin 228) (port : Fin 3)
    (member : port ∈ cpuPortIndices variant index) :
    readToken (machineAssignment variant index) UnifiedReduced.importedConstraintsMemoryPorts[port] =
      ledgerRun old (prefixWrites variant index.val ++ cpuBefore variant index port)
        ((machineCells variant index)[port]) := by
  let earlierWrites := prefixWrites variant index.val ++ cpuBefore variant index port
  let cell := (machineCells variant index)[port]
  have address := ledger_address_invariant earlierWrites old (fun _ => rfl) cell
  have time := ledger_previous_stamp earlierWrites cell
  have words := congrFun (ledger_word_run old earlierWrites) cell
  have values : wordRun (fun cell => (old cell).word) earlierWrites cell = cpuReadWord variant index port := by
    rw [wordRun_append, cpu_before_words]
    exact machine_predecessor_words variant index port
  have clock : previous variant index port = lastStamp earlierWrites cell := by
    have physical := cpu_port_physical variant index port member
    have ordinary : ¬(isCaller index = true ∧ port.val = 1) := by
      rcases physical with other | caller
      · intro bad; exact other bad.2
      · simp [caller]
    simp only [previous, ordinary, ↓reduceIte, earlierWrites, cell, cpuBefore]
  apply token_eq_of_word
  · exact (cpu_native_address variant index port (cpu_port_physical variant index port member)).trans address.symm
  · exact ((cpu_native_read_clocks variant index port).trans (congrArg (fun value : Nat =>
      ((value : ZMod babyBearModulus), 0)) clock)).trans time.symm
  · exact (cpu_native_read_words variant index port).trans (words.trans values).symm

private theorem ledgerRun_append (start : Cell → MemoryToken babyBearModulus) (first second : List Write) :
    ledgerRun start (first ++ second) = ledgerRun (ledgerRun start first) second := by
  exact List.foldl_append

private theorem cpu_ledger_filtered (variant : Variant) (index : Fin 228)
    (start : Cell → MemoryToken babyBearModulus) :
    ledgerSteps start (machineWrites variant index) =
      (cpuPortIndices variant index).map fun port =>
        (ledgerRun start (cpuBefore variant index port) ((machineCells variant index)[port]),
          writeTokenOf (cpuWrite variant index port)) := by
  cases caller : isCaller index
  all_goals simp [machineWrites, cpuPortIndices, caller, cpuBefore, cpuWrite, cpuWrittenWord,
    ledgerSteps, ledgerRun, wordOfNat]

private theorem native_machine_ledger (variant : Variant) (index : Fin 228) :
    nativeMachineSteps variant index =
      ledgerSteps (ledgerRun old (prefixWrites variant index.val)) (machineWrites variant index) := by
  rw [cpu_ledger_filtered]
  have selected := native_selected_iff variant index
  have ports : nativeMachineSteps variant index = (cpuPortIndices variant index).map fun port =>
      (readToken (machineAssignment variant index) UnifiedReduced.importedConstraintsMemoryPorts[port],
        writeToken UnifiedReduced.importedConstraintsTraceColumns (machineAssignment variant index)
          UnifiedReduced.importedConstraintsMemoryPorts[port]) := by
    cases caller : isCaller index
    all_goals simp [nativeMachineSteps, UnifiedReduced.Caller.machinePorts, selected, caller,
      cpuPortIndices, UnifiedReduced.Caller.architecturalPorts, Row.columns, Row.ports,
      UnifiedReduced.importedConstraintsMemoryPorts]
    all_goals first | rfl | exact ⟨rfl, rfl⟩
  rw [ports]
  apply List.map_congr_left
  intro port member
  apply Prod.ext
  · rw [cpu_native_read_token variant index port member, ledgerRun_append]
  · exact cpu_native_write_token variant index port member

/- Raw matching assembled from the preceding proved per-port/row identities. -/

private def nativeRowSteps (variant : Variant) (index : Fin 228) :=
  nativeMachineSteps variant index ++ (rowWorkers index).flatMap (nativeWorkerSteps variant)

private theorem native_row_ledger (variant : Variant) (index : Fin 228) :
    nativeRowSteps variant index =
      ledgerSteps (ledgerRun old (prefixWrites variant index.val)) (rowWrites variant index) := by
  rw [row_ledger_writes, ledgerSteps_append, ← native_machine_ledger]
  unfold nativeRowSteps
  congr 1
  dsimp only [rowWorkers]
  split_ifs with active last
  · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [native_worker_ledger, native_active_call_row index active, ledgerRun_append]
  · have same : index = (227 : Fin 228) := Fin.ext last
    subst index
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [native_worker_ledger]
    change ledgerSteps (ledgerRun old (prefixWrites variant 227 ++ machineWrites variant 227)) _ = _
    rw [ledgerRun_append]
    rfl
  · rfl

private def nativePrefixSteps (variant : Variant) (count : Nat) :=
  (List.finRange count).flatMap fun index =>
    if bound : index.val < 228 then nativeRowSteps variant ⟨index.val, bound⟩ else []

private theorem nativePrefixSteps_succ (variant : Variant) (count : Nat) (bound : count < 228) :
    nativePrefixSteps variant (count + 1) =
      nativePrefixSteps variant count ++ nativeRowSteps variant ⟨count, bound⟩ := by
  unfold nativePrefixSteps
  rw [List.finRange_succ_last, List.flatMap_append, List.flatMap_map]
  simp only [Fin.val_castSucc, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, Fin.val_last, dif_pos bound]

private theorem native_prefix_ledger (variant : Variant) (count : Nat) (bound : count ≤ 228) :
    nativePrefixSteps variant count = ledgerSteps old (prefixWrites variant count) := by
  revert bound
  induction count with
  | zero => intro _; rfl
  | succ count ih =>
      intro bound
      rw [nativePrefixSteps_succ variant count (by omega), prefixWrites_succ variant count (by omega),
        ledgerSteps_append, ih (by omega), native_row_ledger]

private theorem native_ledger_identification (variant : Variant) :
    chronologicalNativeSteps variant = ledgerSteps old (prefixWrites variant 228) := by
  have earlierWrites : nativePrefixSteps variant 228 = chronologicalNativeSteps variant := by
    unfold nativePrefixSteps chronologicalNativeSteps
    apply List.flatMap_congr
    intro index _
    rw [dif_pos index.isLt]
    rfl
  rw [← earlierWrites]
  exact native_prefix_ledger variant 228 (by decide)

/-- Exact shared GPR/RAM token matching for the actual228 CPU rows and56G
workers, with the original native addresses, predecessor times, values and
fresh write times. Scratch/protected stores stay in this single permutation. -/
theorem memory_matching (variant : Variant) :
    ((data variant).machine.initialMemory ++ (data variant).mixedSteps.map Prod.snd).Perm
      ((data variant).machine.terminalMemory ++ (data variant).mixedSteps.map Prod.fst) := by
  have native := native_interleaving variant
  rw [native_ledger_identification] at native
  have writes := native.map Prod.snd
  rw [ledgerSteps_writes] at writes
  have reads := native.map Prod.fst
  rw [ledgerSteps_reads] at reads
  have balance := chronological_balance variant
  exact (writes.symm.append_left (cells.map old)).trans
    (balance.trans (reads.append_left (cells.map (final variant))))

end Tests.PathGLoopNative
