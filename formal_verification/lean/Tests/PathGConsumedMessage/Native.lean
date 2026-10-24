import Tests.PathGConsumedMessage.Core
import Tests.PathGConsumedMessage.Inputs
import Mathlib.Data.List.FinRange

namespace Tests.PathGConsumedMessage
open Airbender Trace Trace.Proofs Arithmetic Reference.RiscV.Sail Reference.Sail
open Airbender.UnifiedReduced.Caller Airbender.UnifiedReduced.Caller.Proofs
open Tests.PathGLoopProgram
open _root_.Sail.ArchSem
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
local instance : MemoryPlatform SailRV32.exception := Tests.upstreamPlatform.airbender

/-- Only the moved store and the four actual final G outputs change terminal
values. Native timestamps still identify the actual last writer of each cell. -/
def finalToken (cell : Cell) : MemoryToken babyBearModulus :=
  if cell = .ram messageAddress then ⟨cell.addressCode, (863, 0), 0⟩
  else if cell = .ram (messageAddress + 32) then ⟨cell.addressCode, (915, 0), Nat.pair 7 0⟩
  else if cell = .ram (stateAddress + 12) then ⟨cell.addressCode, (915, 0), Nat.pair 119 0⟩
  else if cell = .ram (stateAddress + 16) then ⟨cell.addressCode, (915, 0), Nat.pair 3598 57582⟩
  else if cell = .ram (stateAddress + 36) then ⟨cell.addressCode, (915, 0), Nat.pair 1792 30471⟩
  else if cell = .ram (stateAddress + 56) then ⟨cell.addressCode, (915, 0), Nat.pair 1792 30464⟩
  else PathGLoopNative.final .protectedMessage cell

noncomputable def data : RequestTrace babyBearModulus where
  machine := {
    rows := (List.finRange 228).map fun i => ⟨.machine, cpuAssignment i⟩
    rom := UnifiedReduced.Setup.table before
    initial := PCState.boundary 0 (4, 0)
    terminal := PCState.boundary 160 (916, 0)
    initialMemory := PathGLoopNative.cells.map PathGLoopNative.old
    terminalMemory := PathGLoopNative.cells.map finalToken }
  workers := ⟨Delegation.modeledSetup Keccak.Controller.rows,
    (List.finRange 56).map (fun i => ⟨.blakeG, workerAssignment i⟩), [], []⟩
  program := callerProgram

private def cpuSteps (assignment : Nat → ZMod babyBearModulus) :=
  let row : Row babyBearModulus UnifiedFamily := ⟨.machine, assignment⟩
  (machinePorts row).toList.map fun port =>
    (readToken assignment port, writeToken row.columns assignment port)

private def cpuProjection (project : MemoryToken babyBearModulus × MemoryToken babyBearModulus →
    MemoryToken babyBearModulus) (assignment : Nat → ZMod babyBearModulus) :=
  (cpuSteps assignment).map project

private def workerProjection (project : MemoryToken babyBearModulus × MemoryToken babyBearModulus →
    MemoryToken babyBearModulus) (assignment : Nat → ZMod babyBearModulus) :=
  ((⟨.blakeG, assignment⟩ : Delegation.Row babyBearModulus).memorySteps).map project

/-- Replacing one indexed row changes only its contribution to each token count.
The proof leaves the unchanged native prefix opaque. -/
private theorem row_count_patch {ι α : Type} [DecidableEq ι] [DecidableEq α]
    (domain : List ι) (site : ι) (old new : ι → List α)
    (frame : ∀ index, index ≠ site → new index = old index) (token : α) :
    (domain.flatMap new).count token + domain.count site * (old site).count token =
      (domain.flatMap old).count token + domain.count site * (new site).count token := by
  induction domain with
  | nil => simp
  | cons index rest ih =>
      by_cases same : index = site
      · subst index
        simp only [List.flatMap_cons, List.count_append]
        simp only [List.count_cons_self, Nat.add_mul, Nat.one_mul]
        omega
      · have unchanged := frame index same
        simp only [List.flatMap_cons, List.count_append, unchanged]
        simp only [List.count_cons_of_ne same]
        omega

private theorem cpu_count_patch
    (project : MemoryToken babyBearModulus × MemoryToken babyBearModulus →
      MemoryToken babyBearModulus) (token : MemoryToken babyBearModulus) :
    ((List.finRange 228).flatMap fun index => cpuProjection project (cpuAssignment index)).count token +
        (cpuProjection project (PathGLoopNative.machineAssignment .protectedMessage 226)).count token =
      ((List.finRange 228).flatMap fun index =>
        cpuProjection project (PathGLoopNative.machineAssignment .protectedMessage index)).count token +
        (cpuProjection project (cpuAssignment 226)).count token := by
  have patched := row_count_patch (List.finRange 228) (226 : Fin 228)
    (fun index => cpuProjection project (PathGLoopNative.machineAssignment .protectedMessage index))
    (fun index => cpuProjection project (cpuAssignment index)) (fun index different => by
      have actual : index.val ≠ 226 := fun equal => different (Fin.ext equal)
      rw [cpu_unchanged index actual]) token
  simpa only [List.count_finRange, Nat.one_mul] using patched

private theorem worker_count_patch
    (project : MemoryToken babyBearModulus × MemoryToken babyBearModulus →
      MemoryToken babyBearModulus) (token : MemoryToken babyBearModulus) :
    ((List.finRange 56).flatMap fun index => workerProjection project (workerAssignment index)).count token +
        (workerProjection project (PathGLoopNative.workerAssignment .protectedMessage 55)).count token =
      ((List.finRange 56).flatMap fun index =>
        workerProjection project (PathGLoopNative.workerAssignment .protectedMessage index)).count token +
        (workerProjection project (workerAssignment 55)).count token := by
  have patched := row_count_patch (List.finRange 56) (55 : Fin 56)
    (fun index => workerProjection project (PathGLoopNative.workerAssignment .protectedMessage index))
    (fun index => workerProjection project (workerAssignment index)) (fun index different => by
      have actual : index.val ≠ 55 := fun equal => different (Fin.ext equal)
      rw [worker_unchanged index actual]) token
  simpa only [List.count_finRange, Nat.one_mul] using patched

private def touched : List Cell :=
  [.ram messageAddress, .ram (messageAddress + 32), .ram (stateAddress + 12),
    .ram (stateAddress + 16), .ram (stateAddress + 36), .ram (stateAddress + 56)]

private def oldTerminalPatch := touched.map (PathGLoopNative.final .protectedMessage)
private def newTerminalPatch := touched.map finalToken

private theorem terminal_patch :
    ((PathGLoopNative.cells.map (PathGLoopNative.final .protectedMessage)) ++ newTerminalPatch).Perm
      ((PathGLoopNative.cells.map finalToken) ++ oldTerminalPatch) := by
  apply Trace.FiniteFootprint.balance_of_nodup PathGLoopNative.cells touched
    (PathGLoopNative.final .protectedMessage) finalToken oldTerminalPatch newTerminalPatch
    (PathGLoopNative.cells_distinct.of_map Cell.addressCode) (by decide +kernel)
  · intro cell member
    simp only [touched, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide +kernel
  · intro cell _ outside
    simp only [touched, List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
    simp only [finalToken, if_neg outside.1, if_neg outside.2.1, if_neg outside.2.2.1,
      if_neg outside.2.2.2.1, if_neg outside.2.2.2.2.1, if_neg outside.2.2.2.2.2]
  · exact List.perm_append_comm

private def oldLocalReads :=
  cpuProjection Prod.fst (PathGLoopNative.machineAssignment .protectedMessage 226) ++
    workerProjection Prod.fst (PathGLoopNative.workerAssignment .protectedMessage 55)
private def newLocalReads :=
  cpuProjection Prod.fst (cpuAssignment 226) ++ workerProjection Prod.fst (workerAssignment 55)
private def oldLocalWrites :=
  cpuProjection Prod.snd (PathGLoopNative.machineAssignment .protectedMessage 226) ++
    workerProjection Prod.snd (PathGLoopNative.workerAssignment .protectedMessage 55)
private def newLocalWrites :=
  cpuProjection Prod.snd (cpuAssignment 226) ++ workerProjection Prod.snd (workerAssignment 55)

/-- Freeze the three old CPU predecessor clocks once, before the small local
permutation calculation repeats token comparisons. -/
private theorem last_cpu_read_stamps (port : Fin 3) :
    PathGLoopNative.previous .protectedMessage 226 port =
      (#v[895, 22, 863] : Vector Nat 3)[port] := by
  fin_cases port <;> decide +kernel

private def oldStoreStencil (column : Nat) : ZMod babyBearModulus :=
  if column = 34 then 895
  else if column = 40 then 22
  else if column = 46 then 863
  else PathGLoopNative.machineAssignment .protectedMessage 226 column

private theorem old_store_assignment :
    PathGLoopNative.machineAssignment .protectedMessage 226 = oldStoreStencil := by
  funext column
  by_cases first : column = 34
  · subst column
    change (PathGLoopNative.previous .protectedMessage 226 0 : ZMod babyBearModulus) = 895
    rw [last_cpu_read_stamps]
    rfl
  by_cases second : column = 40
  · subst column
    change (PathGLoopNative.previous .protectedMessage 226 1 : ZMod babyBearModulus) = 22
    rw [last_cpu_read_stamps]
    rfl
  by_cases last : column = 46
  · subst column
    change (PathGLoopNative.previous .protectedMessage 226 2 : ZMod babyBearModulus) = 863
    rw [last_cpu_read_stamps]
    rfl
  simp only [oldStoreStencil, if_neg first, if_neg second, if_neg last]

private def lastWorkerStamps : Vector Nat 9 := #v[895, 847, 799, 815, 831, 908, 719, 703, 895]

/-- Each chronological scan is certified once, rather than once per token
comparison in the finite permutation decision. -/
private theorem last_worker_read_stamps (port : Fin 9) :
    PathGLoopNative.workerReadStamp .protectedMessage 55 port = lastWorkerStamps[port] := by
  fin_cases port <;> decide +kernel

private def oldFinalWorkerStencil (column : Nat) : ZMod babyBearModulus :=
  if timestamp : 84 ≤ column ∧ column < 111 then
    if (column - 84) % 3 = 0 then lastWorkerStamps[(⟨(column - 84) / 3, by omega⟩ : Fin 9)]
    else if (column - 84) % 3 = 2 then 1 else 0
  else PathGLoopNative.workerAssignment .protectedMessage 55 column

private theorem old_final_worker_assignment :
    PathGLoopNative.workerAssignment .protectedMessage 55 = oldFinalWorkerStencil := by
  funext column
  by_cases timestamp : 84 ≤ column ∧ column < 111
  · have nonzero : column ≠ 0 := by omega
    have notOne : column ≠ 1 := by omega
    have notThree : column ≠ 3 := by omega
    have notFive : column ≠ 5 := by omega
    have notState : ¬ (7 ≤ column ∧ column < 11) := by omega
    have notMessage : ¬ (11 ≤ column ∧ column < 13) := by omega
    have notPointers : ¬ (column = 14 ∨ column = 32) := by omega
    have notThirtyOne : column ≠ 31 := by omega
    have notInverse : column ≠ 83 := by omega
    simp only [oldFinalWorkerStencil, PathGLoopNative.workerAssignment, timestamp,
      nonzero, notOne, notThree, notFive, notState, notMessage, notPointers,
      notThirtyOne, notInverse, and_self, ↓reduceIte, ↓reduceDIte, last_worker_read_stamps]
  · simp only [oldFinalWorkerStencil, timestamp, ↓reduceDIte]

private def newStoreStencil (column : Nat) : ZMod babyBearModulus :=
  if column = 8 then 32
  else if column = 44 ∨ column = 57 then 96
  else if column = 46 then 719
  else if column = 78 then 24
  else oldStoreStencil column

private theorem new_store_assignment : cpuStoreAssignment = newStoreStencil := by
  funext column
  simp only [cpuStoreAssignment, newStoreStencil, old_store_assignment]

private def finalWorkerStencil (column : Nat) : ZMod babyBearModulus :=
  match column with
  | 17 | 69 | 71 => 119
  | 21 => 3598
  | 22 => 57582
  | 25 | 29 => 1792
  | 26 => 30471
  | 30 => 30464
  | 33 | 41 | 44 | 53 | 62 | 73 | 78 | 81 => 7
  | 79 => 112
  | 80 => 14
  | 82 => 238
  | 102 => 910
  | _ => oldFinalWorkerStencil column

private theorem final_worker_assignment : finalWorkerAssignment = finalWorkerStencil := by
  funext column
  simp only [finalWorkerAssignment, finalWorkerStencil, old_final_worker_assignment]
  rfl

private theorem old_terminal_patch : oldTerminalPatch =
    [⟨(Cell.ram messageAddress).addressCode, (910, 0), Nat.pair 7 0⟩,
      ⟨(Cell.ram (messageAddress + 32)).addressCode, (915, 0), 0⟩,
      ⟨(Cell.ram (stateAddress + 12)).addressCode, (915, 0), 0⟩,
      ⟨(Cell.ram (stateAddress + 16)).addressCode, (915, 0), 0⟩,
      ⟨(Cell.ram (stateAddress + 36)).addressCode, (915, 0), 0⟩,
      ⟨(Cell.ram (stateAddress + 56)).addressCode, (915, 0), 0⟩] := by
  decide +kernel

/-- Only two changed rows and six terminal cells enter this finite check.
The other 282 rows are reused through their existing matching proof. -/
private theorem local_patch :
    (newLocalWrites ++ oldTerminalPatch ++ oldLocalReads).Perm
      (oldLocalWrites ++ newTerminalPatch ++ newLocalReads) := by
  rw [old_terminal_patch]
  have cpu : cpuAssignment 226 = cpuStoreAssignment := rfl
  have worker : workerAssignment 55 = finalWorkerAssignment := rfl
  simp only [newLocalWrites, oldLocalReads, oldLocalWrites, newLocalReads,
    cpu, worker, new_store_assignment, final_worker_assignment,
    old_store_assignment, old_final_worker_assignment]
  decide +kernel


private theorem new_projection
    (project : MemoryToken babyBearModulus × MemoryToken babyBearModulus →
      MemoryToken babyBearModulus) :
    data.mixedSteps.map project =
      ((List.finRange 228).flatMap fun index => cpuProjection project (cpuAssignment index)) ++
      ((List.finRange 56).flatMap fun index => workerProjection project (workerAssignment index)) := by
  simp only [data, RequestTrace.mixedSteps, Delegation.MemoryData.steps,
    cpuProjection, cpuSteps, workerProjection, List.map_append, List.map_flatMap,
    List.flatMap_map]

private theorem old_projection
    (project : MemoryToken babyBearModulus × MemoryToken babyBearModulus →
      MemoryToken babyBearModulus) :
    (PathGLoopNative.data .protectedMessage).mixedSteps.map project =
      ((List.finRange 228).flatMap fun index =>
        cpuProjection project (PathGLoopNative.machineAssignment .protectedMessage index)) ++
      ((List.finRange 56).flatMap fun index =>
        workerProjection project (PathGLoopNative.workerAssignment .protectedMessage index)) := by
  simp only [PathGLoopNative.data, RequestTrace.mixedSteps, Delegation.MemoryData.steps,
    PathGLoopNative.machineRows, PathGLoopNative.workerRows,
    cpuProjection, cpuSteps, workerProjection, List.map_append, List.map_flatMap,
    List.flatMap_map]

/-- Exact initialized matching reuses the original trace and a finite token
patch for the moved store, consumed message and four changed G outputs. -/
theorem memory_matching :
    (data.machine.initialMemory ++ data.mixedSteps.map Prod.snd).Perm
      (data.machine.terminalMemory ++ data.mixedSteps.map Prod.fst) := by
  apply List.perm_iff_count.mpr
  intro token
  have old := (PathGLoopNative.memory_matching .protectedMessage).count_eq token
  have terminal := terminal_patch.count_eq token
  have patchCounts := local_patch.count_eq token
  have cpuReads := cpu_count_patch Prod.fst token
  have cpuWrites := cpu_count_patch Prod.snd token
  have workerReads := worker_count_patch Prod.fst token
  have workerWrites := worker_count_patch Prod.snd token
  rw [old_projection, old_projection] at old
  rw [new_projection, new_projection]
  simp only [oldLocalReads, newLocalReads, oldLocalWrites, newLocalWrites,
    List.count_append] at old terminal patchCounts ⊢
  change (PathGLoopNative.cells.map PathGLoopNative.old).count token + _ =
    (PathGLoopNative.cells.map finalToken).count token + _
  change (PathGLoopNative.cells.map PathGLoopNative.old).count token + _ =
    (PathGLoopNative.cells.map (PathGLoopNative.final .protectedMessage)).count token + _ at old
  omega



private theorem selected (i : Fin 228) :
    Selected (cpuAssignment i) ↔ PathGLoopNative.isCaller i = true := by
  have same : Selected (cpuAssignment i) ↔
      Selected (PathGLoopNative.machineAssignment .protectedMessage i) := by
    by_cases changed : i.val = 226
    · have same : i = (226 : Fin 228) := Fin.ext changed
      subst i
      rfl
    · rw [cpu_unchanged i changed]
  exact same.trans (PathGLoopNative.native_selected_iff .protectedMessage i)

private theorem caller_queries :
    ∀ row ∈ data.callers, (Airbender.UnifiedReduced.Caller.decoderTable data.program).Contains #[]
      (UnifiedReduced.decoderQuery row.assignment) := by
  intro row member
  obtain ⟨included, chosen⟩ := List.mem_filter.mp member
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp included
  have called := (selected i).mp (of_decide_eq_true chosen)
  have different : i.val ≠ 226 := by
    intro same
    have index : i = (226 : Fin 228) := Fin.ext same
    subst i
    contradiction
  have oldMember : (⟨.machine, PathGLoopNative.machineAssignment .protectedMessage i⟩ :
      Row babyBearModulus UnifiedFamily) ∈ (PathGLoopNative.data .protectedMessage).callers := by
    apply List.mem_filter.mpr
    exact ⟨List.mem_map.mpr ⟨i, List.mem_finRange _, rfl⟩,
      decide_eq_true ((PathGLoopNative.native_selected_iff .protectedMessage i).mpr called)⟩
  have sameProgram : data.program = (PathGLoopNative.data .protectedMessage).program := rfl
  rw [sameProgram]
  simpa only [cpuAssignment, different, ↓reduceIte] using
    PathGLoopNative.caller_decoded .protectedMessage _ oldMember

private def decoderStencil (entry : Fin 12) (column : Nat) : ZMod babyBearModulus :=
  let called := decide (entry.val = 6 ∨ entry.val = 11)
  let fields := if called then
      (Tests.DelegationCaller.entry .blakeG).data.mapFamily (fun _ => .machine)
    else (UnifiedReduced.decoderFields (codeEntry .protectedMessage entry).instruction).getD
      ⟨.machine, 0, 0, 0, ⟨0, 0⟩, 0, 0⟩
  if column = 0 then (codeEntry .protectedMessage entry).pc.toNat
  else if column = 2 then 0
  else if column = 4 then 1
  else if column = 5 then fields.rs1.toNat
  else if column = 6 then if called then 0x7c8 else fields.rs2.toNat
  else if column = 7 then fields.rd.toNat
  else if column = 8 then fields.immediate.lo
  else if column = 9 then fields.immediate.hi
  else if column = 10 then fields.funct3
  else if 11 ≤ column ∧ column ≤ 29 then if fields.mask.testBit (column - 11) then 1 else 0
  else 0

/-- Only twelve code stencils are checked; repeated loop occurrences reuse
their stencil without expanding 228 independent decoder proofs. -/
private theorem ordinary_stencil_query (entry : Fin 12)
    (ordinary : decide (entry.val = 6 ∨ entry.val = 11) = false)
    (notStore : entry.val ≠ 10) :
    (UnifiedReduced.decoderTable ordinaryProgram).Contains #[]
      (UnifiedReduced.decoderQuery (decoderStencil entry)) := by
  fin_cases entry
  · exact ⟨(0 : Fin 10), by decide +kernel⟩
  · exact ⟨(1 : Fin 10), by decide +kernel⟩
  · exact ⟨(2 : Fin 10), by decide +kernel⟩
  · exact ⟨(3 : Fin 10), by decide +kernel⟩
  · exact ⟨(4 : Fin 10), by decide +kernel⟩
  · exact ⟨(5 : Fin 10), by decide +kernel⟩
  · exact Bool.noConfusion ordinary
  · exact ⟨(6 : Fin 10), by decide +kernel⟩
  · exact ⟨(7 : Fin 10), by decide +kernel⟩
  · exact ⟨(8 : Fin 10), by decide +kernel⟩
  · exact False.elim (notStore rfl)
  · exact Bool.noConfusion ordinary

private theorem ordinary_queries :
    ∀ row ∈ data.machine.rows, row ∉ data.callers →
      (UnifiedReduced.decoderTable ordinaryProgram).Contains #[] row.decoderQuery := by
  intro row member noncaller
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp member
  have ordinary : PathGLoopNative.isCaller i = false := by
    apply Bool.eq_false_iff.mpr
    intro called
    apply noncaller
    apply List.mem_filter.mpr
    exact ⟨List.mem_map.mpr ⟨i, List.mem_finRange _, rfl⟩,
      decide_eq_true ((selected i).mpr called)⟩
  by_cases changed : i.val = 226
  · have same : i = (226 : Fin 228) := Fin.ext changed
    subst i
    exact ⟨(9 : Fin 10), by decide +kernel⟩
  · have notStore : (rowCodeIndex i).val ≠ 10 := by
      intro equal
      apply changed
      have bound := i.isLt
      have remainder := Nat.mod_lt (i.val - 6) (by decide : 0 < 4)
      dsimp only [rowCodeIndex] at equal
      split_ifs at equal <;> omega
    change (UnifiedReduced.decoderTable ordinaryProgram).Contains #[]
      (UnifiedReduced.decoderQuery (cpuAssignment i))
    rw [cpu_unchanged i changed]
    change (UnifiedReduced.decoderTable ordinaryProgram).Contains #[]
      (UnifiedReduced.decoderQuery (decoderStencil (rowCodeIndex i)))
    exact ordinary_stencil_query _ ordinary notStore

private theorem cpu_boundaries (index : Fin 228) :
    (⟨.machine, cpuAssignment index⟩ : Row babyBearModulus UnifiedFamily).start =
        (⟨.machine, PathGLoopNative.machineAssignment .protectedMessage index⟩ :
          Row babyBearModulus UnifiedFamily).start ∧
      (⟨.machine, cpuAssignment index⟩ : Row babyBearModulus UnifiedFamily).finish =
        (⟨.machine, PathGLoopNative.machineAssignment .protectedMessage index⟩ :
          Row babyBearModulus UnifiedFamily).finish := by
  by_cases changed : index.val = 226
  · have same : index = (226 : Fin 228) := Fin.ext changed
    subst index
    exact ⟨rfl, rfl⟩
  · rw [cpu_unchanged index changed]
    exact ⟨rfl, rfl⟩

private theorem caller_rows_frame (domain : List (Fin 228)) :
    ((domain.map fun index => (⟨.machine, cpuAssignment index⟩ :
      Row babyBearModulus UnifiedFamily)).filter fun row => decide (Selected row.assignment)) =
    ((domain.map fun index => (⟨.machine, PathGLoopNative.machineAssignment .protectedMessage index⟩ :
      Row babyBearModulus UnifiedFamily)).filter fun row => decide (Selected row.assignment)) := by
  induction domain with
  | nil => rfl
  | cons index rest ih =>
      simp only [List.map_cons, List.filter_cons]
      by_cases changed : index.val = 226
      · have same : index = (226 : Fin 228) := Fin.ext changed
        subst index
        have excluded : ¬ Selected (cpuAssignment 226) := by
          rw [selected]
          decide +kernel
        have oldExcluded : ¬ Selected (PathGLoopNative.machineAssignment .protectedMessage 226) := by
          rw [PathGLoopNative.native_selected_iff]
          decide +kernel
        simpa only [excluded, oldExcluded, decide_false, Bool.false_eq_true, ↓reduceIte] using ih
      · rw [cpu_unchanged index changed, ih]

private theorem callers_frame : data.callers = (PathGLoopNative.data .protectedMessage).callers := by
  exact caller_rows_frame (List.finRange 228)

private theorem worker_fulfillment_frame (index : Fin 56) :
    Delegation.Requests.fulfillment ⟨.blakeG, workerAssignment index⟩ =
      Delegation.Requests.fulfillment ⟨.blakeG, PathGLoopNative.workerAssignment .protectedMessage index⟩ := by
  by_cases changed : index.val = 55
  · have same : index = (55 : Fin 56) := Fin.ext changed
    subst index
    rfl
  · rw [worker_unchanged index changed]

/-- Acceptance is proved from actual imported constraints, decoding, requests
and the same architectural memory permutation; no result premise is supplied. -/
theorem accepted : MixedMemoryAccepted data ordinaryProgram := by
  refine ⟨?_, ordinary_queries, memory_matching⟩
  constructor
  · intro row member
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp member
    exact Verification.holds_append (cpu_core i) (cpu_timestamps i)
  · intro row member
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp member
    change cpuAssignment i 4 = 1
    by_cases same : i.val = 226
    · have index : i = (226 : Fin 228) := Fin.ext same
      subst i
      rfl
    · rw [cpu_unchanged i same]
      rfl
  · have starts : data.machine.rows.map Row.start =
        (PathGLoopNative.data .protectedMessage).machine.rows.map Row.start := by
      simp only [data, PathGLoopNative.data, PathGLoopNative.machineRows, List.map_map]
      apply List.map_congr_left
      intro index _
      exact (cpu_boundaries index).1
    have finishes : data.machine.rows.map Row.finish =
        (PathGLoopNative.data .protectedMessage).machine.rows.map Row.finish := by
      simp only [data, PathGLoopNative.data, PathGLoopNative.machineRows, List.map_map]
      apply List.map_congr_left
      intro index _
      exact (cpu_boundaries index).2
    rw [starts, finishes]
    exact (PathGLoopNative.checks .protectedMessage).states
  · exact caller_queries
  · intro row member
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp member
    exact Verification.holds_append (worker_core i) (worker_timestamps i)
  · intro row member
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp member
    change workerAssignment i 0 = 1
    by_cases same : i.val = 55
    · have index : i = (55 : Fin 56) := Fin.ext same
      subst i
      rfl
    · rw [worker_unchanged i same]
      rfl
  · have calls : data.calls = (PathGLoopNative.data .protectedMessage).calls := by
      simp only [RequestTrace.calls, callers_frame]
    have fulfillments : data.fulfillments =
        (PathGLoopNative.data .protectedMessage).fulfillments := by
      simp only [RequestTrace.fulfillments, data, PathGLoopNative.data,
        PathGLoopNative.workerRows, List.map_map]
      apply List.map_congr_left
      intro index _
      exact worker_fulfillment_frame index
    rw [calls, fulfillments]
    exact PathGLoopNative.request_matching .protectedMessage

/-- The altered store is decoded from its actual installed bytes. Initialization
and all tracked cells remain the same zero public memory profile. -/
theorem inputs : MixedMemoryInputs data ordinaryProgram before [128, 156]
    [0, 4, 8, 12, 16, 20, 132, 144, 148, 152] PathGLoopNative.cells := by
  refine ⟨⟨caller_image, ?_, ?_⟩, ordinary_image, initialization,
    PathGLoopNative.cells_distinct, PathGLoopNative.cells_aligned, rfl, rfl, ?_⟩
  · change 4 < timestampBase ∧ 0 < timestampBase
    norm_num [timestampBase]
  · change (4 : Nat) % 4 = 0
    decide +kernel
  · intro worker member family
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    cases family



end Tests.PathGConsumedMessage
