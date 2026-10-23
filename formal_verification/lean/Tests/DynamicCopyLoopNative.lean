import Tests.DynamicCopyLoopProgram
import Mathlib.Data.List.FinRange
import Tests.DelegationCaller
import Airbender.Review.Trace.UnifiedReduced.MixedMemory
import Airbender.Review.Trace.UnifiedReduced.NativeMixedROM
import Airbender.Proofs.UnifiedReduced.Claims
import Airbender.Proofs.Bigint.Claims

namespace Tests.DynamicCopyLoopNative
open Airbender Trace Arithmetic Reference.RiscV.Sail Reference.Sail
open _root_.Sail.ArchSem
set_option warningAsError true
set_option Elab.async false
local instance : MemoryPlatform SailRV32.exception := Tests.upstreamPlatform.airbender

/-- Exactly all32GPRs and the two disjoint8word blocks. Code is public ROM,
separate from these architectural data tokens. -/
def cells : List Cell :=
  (List.finRange 32).map (fun i => .register (BitVec.ofNat 5 i.val)) ++
  (List.finRange 8).map (fun i => .ram
    (DynamicCopyLoopProgram.destinationAddress + 4 * BitVec.ofNat 32 i.val)) ++
  (List.finRange 8).map (fun i => .ram
    (DynamicCopyLoopProgram.sourceAddress + 4 * BitVec.ofNat 32 i.val))

/-- The actual public CSR encoding and metadata, relocated to its code address. -/
def callerEntry : UnifiedReduced.Caller.ProgramEntry :=
  { Tests.DelegationCaller.entry .bigint with pc := 132 }
def callerProgram : List UnifiedReduced.Caller.ProgramEntry := [callerEntry]

/-- Distinct public ordinary entries can occur several times on the native path. -/
def ordinaryIndex (index : Fin 16) : Option (Fin 11) :=
  match index.val with
  | 0 => some 0 | 1 => some 1 | 2 => some 2 | 3 => some 3
  | 4 => some 4 | 5 => some 5 | 6 => some 6 | 7 => none
  | 8 => some 7 | 9 => some 8 | 10 => some 6 | 11 => none
  | 12 => some 7 | 13 => some 8 | 14 => some 9 | _ => some 10

/-- Witness decoder columns reuse the original-decoder-backed public entries.
Their native query memberships remain separate proof obligations. -/
def metadata (index : Fin 16) : DecoderData UnifiedFamily :=
  match ordinaryIndex index with
  | some entry => (DynamicCopyLoopProgram.ordinaryEntry entry).data
  | none => callerEntry.data.mapFamily (fun _ => .machine)

private structure Sample where
  pc : Nat
  next : Nat
  clock : Nat
  previous0 : Nat
  previous1 : Nat
  previous2 : Nat
  source0 : Nat
  source1 : Nat
  oldDestination : Nat
  newDestination : Nat

/-- Concrete candidate port values and recomputed predecessor clocks. The
acceptance proof checks these against the actual imported port expressions. -/
private def sample (index : Fin 16) : Sample :=
  match index.val with
  | 0 => ⟨0, 4, 4, 0, 4, 0, 0, 0, 0, 2⟩
  | 1 => ⟨4, 8, 8, 5, 8, 0, 0, 0, 0, 33554432⟩
  | 2 => ⟨8, 12, 12, 10, 9, 0, 33554432, 0, 0, 33554464⟩
  | 3 => ⟨12, 16, 16, 13, 16, 0, 0, 0, 0, 7⟩
  | 4 => ⟨16, 20, 20, 14, 18, 0, 33554464, 7, 0, 7⟩
  | 5 => ⟨20, 128, 24, 17, 24, 25, 0, 0, 0, 0⟩
  | 6 => ⟨128, 132, 28, 26, 28, 0, 0, 0, 0, 128⟩
  | 7 => ⟨132, 136, 32, 29, 0, 32, 0, 0, 0, 0⟩
  | 8 => ⟨136, 140, 36, 6, 34, 36, 2, 0, 2, 1⟩
  | 9 => ⟨140, 128, 40, 38, 37, 41, 1, 0, 0, 0⟩
  | 10 => ⟨128, 132, 44, 42, 44, 35, 0, 0, 0, 128⟩
  | 11 => ⟨132, 136, 48, 45, 0, 48, 0, 0, 0, 0⟩
  | 12 => ⟨136, 140, 52, 40, 50, 52, 1, 0, 1, 0⟩
  | 13 => ⟨140, 144, 56, 54, 53, 57, 0, 0, 0, 0⟩
  | 14 => ⟨144, 152, 60, 58, 60, 0, 0, 0, 0, 148⟩
  | _ => ⟨152, 156, 64, 62, 61, 65, 148, 0, 0, 0⟩

private def family2 (index : Fin 16) : Bool :=
  index.val = 5 || index.val = 9 || index.val = 13 || index.val = 14 || index.val = 15
private def branch (index : Fin 16) : Bool := index.val = 9 || index.val = 13
private def indirect (index : Fin 16) : Bool := index.val = 15
private def branchTaken (index : Fin 16) : Bool := index.val = 9
private def saved (index : Fin 16) : Nat :=
  if branch index then (sample index).source0 else (sample index).pc + 4

/-- All richer unified columns, including the shared carry/register/lookup
witnesses. Word limbs are split in Nat before their field embedding; dividing
inside ZMod would produce field inverses instead of high limbs. No gate,
lookup, or timestamp check is removed from acceptance. -/
def machineAssignment (index : Fin 16) (column : Nat) : ZMod babyBearModulus :=
  let row := sample index
  let fields := metadata index
  if column = 0 then row.pc
  else if column = 2 then row.clock
  else if column = 4 || column = 130 || column = 131 || column = 132 || column = 133 then 1
  else if column = 5 then fields.rs1.toNat
  else if column = 6 then if index.val = 7 || index.val = 11 then 0x7ca else fields.rs2.toNat
  else if column = 7 then fields.rd.toNat
  else if column = 8 then fields.immediate.lo
  else if column = 9 then fields.immediate.hi
  else if column = 10 then fields.funct3
  else if 11 ≤ column && column ≤ 29 then if fields.mask.testBit (column - 11) then 1 else 0
  else if column = 30 then row.next
  else if column = 32 then row.clock + 4
  else if column = 34 then row.previous0
  else if column = 36 then ((row.source0 % 65536 : Nat) : ZMod babyBearModulus)
  else if column = 37 then ((row.source0 / 65536 : Nat) : ZMod babyBearModulus)
  else if column = 38 then if index.val = 7 || index.val = 11 then 0x7ca else fields.rs2.toNat
  else if column = 40 then row.previous1
  else if column = 42 then ((row.source1 % 65536 : Nat) : ZMod babyBearModulus)
  else if column = 43 then ((row.source1 / 65536 : Nat) : ZMod babyBearModulus)
  else if column = 44 then if index.val = 4 then 32 else fields.rd.toNat
  else if column = 45 then if index.val = 4 then 512 else 0
  else if column = 46 then row.previous2
  else if column = 48 then ((row.oldDestination % 65536 : Nat) : ZMod babyBearModulus)
  else if column = 49 then ((row.oldDestination / 65536 : Nat) : ZMod babyBearModulus)
  else if column = 50 then ((row.newDestination % 65536 : Nat) : ZMod babyBearModulus)
  else if column = 51 then ((row.newDestination / 65536 : Nat) : ZMod babyBearModulus)
  else if column = 52 || column = 53 then if index.val = 8 || index.val = 12 then 1 else 0
  else if column = 54 || column = 55 then if branchTaken index then 1 else 0
  else if column = 57 then if index.val = 4 then 32 else if index.val = 13 then 1 else 0
  else if column = 58 then if index.val = 4 then 512 else 0
  else if column = 59 || column = 82 || column = 112 then if branchTaken index then 1 else 0
  else if column = 78 then if index.val = 4 then 8 else if family2 index then saved index else 0
  else if column = 80 then (row.source0 : ZMod babyBearModulus) * row.source1 * 943718400
  else if column = 81 || column = 120 || column = 122 then if family2 index then row.next else 0
  else if column = 83 then if index.val = 14 then 1 else 0
  else if column = 85 then if family2 index && index.val != 14 then 1 else 0
  else if column = 86 then if index.val = 4 then 448 else 0
  else if column = 88 then if family2 index then 1 else 0
  else if column = 89 then if family2 index then saved index else 0
  else if column = 90 then if index.val = 13 then 1 else 0
  else if column = 92 || column = 101 then if family2 index then 5 else 0
  else if column = 110 then if family2 index then 51 else 0
  else if column = 111 then if index.val = 9 then 16 else if index.val = 13 then 24 else 0
  else if column = 119 then if family2 index then 2 else 0
  else if column = 129 then if family2 index then 0 else 1
  else 0

def machineRows : List (Row babyBearModulus UnifiedFamily) :=
  (List.finRange 16).map fun index => ⟨.machine, machineAssignment index⟩

/-- Each actual COPY worker consumes x12=128, copies the nonzero right operand,
and returns zero control. Validity of this constructed command does not settle
F02 for arbitrary accepted controls. -/
def workerAssignment (index : Fin 2) (column : Nat) : ZMod babyBearModulus :=
  if column = 0 || column = 66 || column = 212 || column = 214 || column = 215 then 1
  else if column = 1 then if index.val = 0 then 33 else 49
  else if column = 4 || column = 38 then 512
  else if column = 37 then 32
  else if column = 55 then 128
  else if column = 5 || column = 99 then if index.val = 0 then 0 else 7
  else if column = 7 || column = 39 || column = 67 || column = 115 || column = 194 then 7
  else if column = 131 || column = 163 then if index.val = 0 then 0 else 49
  else if 217 ≤ column && column < 274 then
    if (column - 217) % 3 = 2 then 1
    else if (column - 217) % 3 = 1 then 0
    else if index.val = 1 then if column = 271 then 46 else 35
    else if column = 217 then 12
    else if column = 244 then 20
    else if column = 247 then 22
    else if column = 271 then 30
    else 0
  else 0

def workerRows : List (Delegation.Row babyBearModulus) :=
  (List.finRange 2).map fun index => ⟨.bigint, workerAssignment index⟩

def old (cell : Cell) : MemoryToken babyBearModulus := cell.initialToken 0

def final (cell : Cell) : MemoryToken babyBearModulus :=
  match cell with
  | .register register =>
    let stamp := if register = 0 then 66 else if register = 1 then 64
      else if register = 2 then 21 else if register = 5 then 56
      else if register = 10 || register = 11 || register = 12 then 51 else 0
    let value : Word := if register = 1 then ⟨148, 0⟩ else if register = 2 then ⟨7, 0⟩
      else if register = 10 then ⟨0, 512⟩ else if register = 11 then ⟨32, 512⟩ else ⟨0, 0⟩
    ⟨cell.addressCode, (stamp, 0), Nat.pair value.lo value.hi⟩
  | .ram address =>
    if 33554432 ≤ address.toNat && address.toNat < 33554496 then
      ⟨cell.addressCode, (51, 0), Nat.pair
        (if address = DynamicCopyLoopProgram.destinationAddress ||
          address = DynamicCopyLoopProgram.sourceAddress then 7 else 0) 0⟩
    else old cell

/-- Concrete candidate native data; acceptance and actual public initialization
are proved separately below. The worker-only seed/terminal fields are unused by
the shared architectural permutation. -/
noncomputable def data : UnifiedReduced.Caller.RequestTrace babyBearModulus where
  machine := {
    rows := machineRows
    rom := UnifiedReduced.Setup.table DynamicCopyLoopProgram.before
    initial := PCState.boundary 0 (4, 0)
    terminal := PCState.boundary 156 (68, 0)
    initialMemory := cells.map old
    terminalMemory := cells.map final }
  workers := ⟨Delegation.modeledSetup Keccak.Controller.rows, workerRows, [], []⟩
  program := callerProgram

theorem machine_count : data.machine.rows.length = 16 := by decide +kernel
theorem worker_count : data.workers.rows.length = 2 := by decide +kernel

theorem native_path : data.machine.rows.map (fun row => row.start.word.toBitVec) =
    DynamicCopyLoopProgram.pathPCs := by decide +kernel

theorem memory_step_count : data.mixedSteps.length = 84 := by decide +kernel

/-- Both sides of exact logical architectural matching have132actual tokens. -/
theorem memory_token_counts :
    (data.machine.initialMemory ++ data.mixedSteps.map Prod.snd).length = 132 ∧
    (data.machine.terminalMemory ++ data.mixedSteps.map Prod.fst).length = 132 := by
  decide +kernel

/-- A concrete reordering certificate has no token semantics of its own.
The inverse identities and every imported-token pair are checked below. -/
private def matchingIndices : Vector (Fin 132) 132 :=
  #v[48, 90, 59, 3, 4, 50, 6, 7, 8, 9, 53, 56, 68, 13, 14, 15,
    16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
    95, 96, 97, 98, 99, 100, 101, 102, 62, 105, 106, 107, 108, 109, 110, 111,
    49, 51, 71, 52, 55, 54, 94, 57, 60, 58, 63, 61, 103, 2, 104, 64,
    65, 66, 67, 69, 112, 70, 72, 73, 75, 74, 82, 76, 77, 78, 80, 131,
    81, 83, 84, 86, 85, 5, 87, 88, 89, 92, 91, 1, 93, 0, 113, 114,
    115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130,
    79, 10, 32, 33, 34, 35, 36, 37, 38, 39, 11, 40, 41, 42, 43, 44,
    45, 46, 47, 12]
private def inverseMatchingIndices : Vector (Fin 132) 132 :=
  #v[93, 91, 61, 3, 4, 85, 6, 7, 8, 9, 113, 122, 131, 13, 14, 15,
    16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
    114, 115, 116, 117, 118, 119, 120, 121, 123, 124, 125, 126, 127, 128, 129, 130,
    0, 48, 5, 49, 51, 10, 53, 52, 11, 55, 57, 2, 56, 59, 40, 58,
    63, 64, 65, 66, 12, 67, 69, 50, 70, 71, 73, 72, 75, 76, 77, 112,
    78, 80, 74, 81, 82, 84, 83, 86, 87, 88, 1, 90, 89, 92, 54, 32,
    33, 34, 35, 36, 37, 38, 39, 60, 62, 41, 42, 43, 44, 45, 46, 47,
    68, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108,
    109, 110, 111, 79]

private def matchingPermutation : Equiv.Perm (Fin 132) where
  toFun index := matchingIndices[index]
  invFun index := inverseMatchingIndices[index]
  left_inv := by intro index; fin_cases index <;> decide +kernel
  right_inv := by intro index; fin_cases index <;> decide +kernel

private noncomputable def leftTokens : List (MemoryToken babyBearModulus) :=
  data.machine.initialMemory ++ data.mixedSteps.map Prod.snd
private noncomputable def rightTokens : List (MemoryToken babyBearModulus) :=
  data.machine.terminalMemory ++ data.mixedSteps.map Prod.fst

private noncomputable def leftToken (index : Fin 132) : MemoryToken babyBearModulus :=
  leftTokens[index.val]'(by have length := memory_token_counts.1; change leftTokens.length = 132 at length; omega)
private noncomputable def rightToken (index : Fin 132) : MemoryToken babyBearModulus :=
  rightTokens[index.val]'(by have length := memory_token_counts.2; change rightTokens.length = 132 at length; omega)

private theorem ofFn_get_length {α : Type} (values : List α) {length : Nat}
    (size : values.length = length) :
    List.ofFn (fun index : Fin length => values[index.val]'(by omega)) = values := by
  subst length
  exact List.ofFn_getElem

private theorem token_eq {left right : MemoryToken p}
    (address : left.address = right.address)
    (low : left.time.1 = right.time.1) (high : left.time.2 = right.time.2)
    (value : left.value = right.value) : left = right := by
  have time : left.time = right.time := Prod.ext low high
  cases left
  cases right
  cases address
  cases time
  cases value
  rfl

private theorem store_rs2 : (metadata 4).rs2 = 2 := by
  change ((UnifiedReduced.decoderFields (.STORE (0, .Regidx 2, .Regidx 11, 4))).get (by decide)).rs2 = 2
  rfl

private theorem store_mask : (metadata 4).mask = 262144 := by
  change ((UnifiedReduced.decoderFields (.STORE (0, .Regidx 2, .Regidx 11, 4))).get (by decide)).mask = 262144
  rfl

private theorem jalr_rs1 : (metadata 15).rs1 = 1 := by
  change ((UnifiedReduced.decoderFields (.JALR (8, .Regidx 1, .Regidx 0))).get (by decide)).rs1 = 1
  rfl

/-- Expose the imported readonly token one scalar field at a time. In particular
its value code is Nat.pair7,0, not a large token/list Boolean reduction. -/
private theorem refreshed_x2 :
    writeToken UnifiedReduced.importedConstraintsTraceColumns (machineAssignment 4)
      UnifiedReduced.importedConstraintsMemoryPorts[1] = final (.register 2) := by
  apply token_eq
  · change Nat.pair (machineAssignment 4 28).val
      (Nat.pair (machineAssignment 4 38).val (machineAssignment 4 39).val) =
        Nat.pair 0 (Nat.pair 2 0)
    have space : machineAssignment 4 28 = 0 := by
      change (if (metadata 4).mask.testBit 17 then (1 : ZMod babyBearModulus) else 0) = 0
      rw [store_mask]
      decide +kernel
    have address : machineAssignment 4 38 = 2 := by
      change ((metadata 4).rs2.toNat : ZMod babyBearModulus) = 2
      rw [store_rs2]
      decide +kernel
    have upper : machineAssignment 4 39 = 0 := by norm_num [machineAssignment, sample]
    rw [space, address, upper]
    rfl
  · change machineAssignment 4 2 + 1 = 21
    norm_num [machineAssignment, sample]
  · change machineAssignment 4 3 = 0
    norm_num [machineAssignment, sample]
  · change Nat.pair (machineAssignment 4 42).val (machineAssignment 4 43).val = Nat.pair 7 0
    have lower : machineAssignment 4 42 = 7 := by norm_num [machineAssignment, sample]
    have upper : machineAssignment 4 43 = 0 := by norm_num [machineAssignment, sample]
    rw [lower, upper]
    rfl

private theorem refreshed_x1 :
    writeToken UnifiedReduced.importedConstraintsTraceColumns (machineAssignment 15)
      UnifiedReduced.importedConstraintsMemoryPorts[0] = final (.register 1) := by
  apply token_eq
  · change Nat.pair 0 (Nat.pair (machineAssignment 15 5).val 0) = Nat.pair 0 (Nat.pair 1 0)
    have address : machineAssignment 15 5 = 1 := by
      change ((metadata 15).rs1.toNat : ZMod babyBearModulus) = 1
      rw [jalr_rs1]
      decide +kernel
    rw [address]
    rfl
  · change machineAssignment 15 2 + 0 = 64
    norm_num [machineAssignment, sample]
  · change machineAssignment 15 3 = 0
    norm_num [machineAssignment, sample]
  · change Nat.pair (machineAssignment 15 36).val (machineAssignment 15 37).val = Nat.pair 148 0
    have lower : machineAssignment 15 36 = 148 := by norm_num [machineAssignment, sample]
    have upper : machineAssignment 15 37 = 0 := by norm_num [machineAssignment, sample]
    rw [lower, upper]
    rfl

/-- Each equality checks actual readToken/writeToken address, both timestamp
limbs and full value code. A wrong ledger/certificate fails at its specific pair. -/
private theorem matching_tokens (index : Fin 132) :
    leftToken index = rightToken (matchingPermutation index) := by
  fin_cases index
  case «61» =>
    change writeToken UnifiedReduced.importedConstraintsTraceColumns (machineAssignment 4)
      UnifiedReduced.importedConstraintsMemoryPorts[1] = final (.register 2)
    exact refreshed_x2
  case «91» =>
    change writeToken UnifiedReduced.importedConstraintsTraceColumns (machineAssignment 15)
      UnifiedReduced.importedConstraintsMemoryPorts[0] = final (.register 1)
    exact refreshed_x1
  all_goals decide +kernel

/-- Constructive132token matching: prove the finite reordering bijective, then
transport its132kernel-checked actual token equalities. No MemoryToken.isPerm
reduction or assumed token/worker/read equality is used. -/
theorem memory_matching :
    (data.machine.initialMemory ++ data.mixedSteps.map Prod.snd).Perm
      (data.machine.terminalMemory ++ data.mixedSteps.map Prod.fst) := by
  have left : List.ofFn leftToken = leftTokens := ofFn_get_length _ memory_token_counts.1
  have right : List.ofFn rightToken = rightTokens := ofFn_get_length _ memory_token_counts.2
  have paired : leftToken = rightToken ∘ matchingPermutation := funext matching_tokens
  change leftTokens.Perm rightTokens
  rw [← left, ← right, paired]
  exact matchingPermutation.ofFn_comp_perm rightToken


/-- Original public bytes construct the one full-width CSR entry. -/
theorem caller_image : UnifiedReduced.Caller.programImage DynamicCopyLoopProgram.before [132] =
    some callerProgram := by
  exact Trace.Proofs.program_image_run_singleton_of_reads Delegation.Caller.decoderFields
    DynamicCopyLoopProgram.before callerEntry (DynamicCopyLoopProgram.fetch 7)
    (DynamicCopyLoopProgram.original_decode 7 DynamicCopyLoopProgram.before)
    (Tests.DelegationCaller.metadata .bigint)

private theorem mixed_fields (index : Fin 11) :
    UnifiedReduced.Mixed.decoderFields (DynamicCopyLoopProgram.ordinaryEntry index).instruction =
      some (DynamicCopyLoopProgram.ordinaryEntry index).data := by
  unfold UnifiedReduced.Mixed.decoderFields
  rw [DynamicCopyLoopProgram.ordinary_fields]
  rfl

private theorem mixed_entry_run (index : Fin 11) :
    programEntryRunWith UnifiedReduced.Mixed.decoderFields DynamicCopyLoopProgram.before
      (DynamicCopyLoopProgram.ordinaryEntry index).pc =
        some (DynamicCopyLoopProgram.ordinaryEntry index) :=
  Trace.Proofs.program_entry_run_of_reads _ _ _ _ _ _
    (DynamicCopyLoopProgram.ordinary_source index).bytes
    (DynamicCopyLoopProgram.ordinary_source index).decoded (mixed_fields index)

theorem ordinary_image : UnifiedReduced.Mixed.programImage DynamicCopyLoopProgram.before
    [0, 4, 8, 12, 16, 20, 128, 136, 140, 144, 152] = some DynamicCopyLoopProgram.ordinaryProgram := by
  change programImageRunWith UnifiedReduced.Mixed.decoderFields DynamicCopyLoopProgram.before
    [(DynamicCopyLoopProgram.ordinaryEntry 0).pc, (DynamicCopyLoopProgram.ordinaryEntry 1).pc,
      (DynamicCopyLoopProgram.ordinaryEntry 2).pc, (DynamicCopyLoopProgram.ordinaryEntry 3).pc,
      (DynamicCopyLoopProgram.ordinaryEntry 4).pc, (DynamicCopyLoopProgram.ordinaryEntry 5).pc,
      (DynamicCopyLoopProgram.ordinaryEntry 6).pc, (DynamicCopyLoopProgram.ordinaryEntry 7).pc,
      (DynamicCopyLoopProgram.ordinaryEntry 8).pc, (DynamicCopyLoopProgram.ordinaryEntry 9).pc,
      (DynamicCopyLoopProgram.ordinaryEntry 10).pc] = _
  simp only [programImageRunWith, List.mapM_cons, List.mapM_nil,
    mixed_entry_run 0, mixed_entry_run 1, mixed_entry_run 2, mixed_entry_run 3,
    mixed_entry_run 4, mixed_entry_run 5, mixed_entry_run 6, mixed_entry_run 7,
    mixed_entry_run 8, mixed_entry_run 9, mixed_entry_run 10, bind, Option.bind, pure]
  rfl

private theorem cells_zero (cell : Cell) (member : cell ∈ cells) :
    cell.read DynamicCopyLoopProgram.before = .ok 0 DynamicCopyLoopProgram.before := by
  simp only [cells, List.mem_append, List.mem_map] at member
  rcases member with (⟨index, _, rfl⟩ | ⟨index, _, rfl⟩) | ⟨index, _, rfl⟩
  · exact DynamicCopyLoopProgram.registers_zero _
  · exact DynamicCopyLoopProgram.destination_block_zero index
  · exact DynamicCopyLoopProgram.source_block_zero index

/-- This physical initialization is constructed from the real installed public
state. No source value, pointer, control, or successful-execution premise is used. -/
theorem initialization : initialImage DynamicCopyLoopProgram.before cells = some data.machine.initialMemory := by
  have allZero (domain : List Cell)
      (reads : ∀ cell ∈ domain, cell.read DynamicCopyLoopProgram.before = .ok 0 DynamicCopyLoopProgram.before) :
      initialImage DynamicCopyLoopProgram.before domain = some (domain.map old) := by
    induction domain with
    | nil => rfl
    | cons cell rest ih =>
      have next := ih (fun item member => reads item (List.mem_cons_of_mem cell member))
      simp only [initialImage] at next
      simp only [initialImage, List.mapM_cons, reads cell List.mem_cons_self, bind, Option.bind,
        next, List.map_cons, old]
      rfl
  exact allZero cells cells_zero

/-- Both blocks stay in the current physical RAM scope, above the4MiB ROM split. -/
theorem ram_scope (address : BitVec 32) (member : Cell.ram address ∈ cells) :
    ROM.limit ≤ address.toNat ∧ address.toNat + 4 ≤ 2 ^ 30 := by
  simp only [cells, List.mem_append, List.mem_map] at member
  rcases member with (⟨index, _, same⟩ | ⟨index, _, same⟩) | ⟨index, _, same⟩
  · cases same
  · cases same
    fin_cases index <;> decide +kernel
  · cases same
    fin_cases index <;> decide +kernel

theorem cells_aligned (cell : Cell) (member : cell ∈ cells) : cell.Aligned := by
  simp only [cells, List.mem_append, List.mem_map] at member
  rcases member with (⟨index, _, rfl⟩ | ⟨index, _, rfl⟩) | ⟨index, _, rfl⟩
  · trivial
  · dsimp only [Cell.Aligned]
    fin_cases index <;> decide +kernel
  · dsimp only [Cell.Aligned]
    fin_cases index <;> decide +kernel

/-- Only concrete public boot/model inputs. The blake-round side condition is
empty because these two actual workers are bigint workers. -/
theorem inputs : UnifiedReduced.Caller.MixedMemoryInputs data DynamicCopyLoopProgram.ordinaryProgram
    DynamicCopyLoopProgram.before [132] [0, 4, 8, 12, 16, 20, 128, 136, 140, 144, 152] cells := by
  refine ⟨⟨caller_image, ?_, ?_⟩, ordinary_image, initialization, ?_, cells_aligned, rfl, rfl, ?_⟩
  · change 4 < timestampBase ∧ 0 < timestampBase
    norm_num [timestampBase]
  · decide +kernel
  · decide +kernel
  · intro worker member family
    change worker ∈ workerRows at member
    rcases List.mem_map.mp member with ⟨index, _, rfl⟩
    cases family

/-- A small kernel-computed Boolean records every actual imported assertion.
Lookup membership is proved separately, without enumerating a large setup table. -/
private def equationsCheck (assignment : Nat → ZMod babyBearModulus)
    (operations : List (FlatOperation (ZMod babyBearModulus))) : Bool :=
  (FlatOperation.constraints operations).all fun expression =>
    decide (Verification.environment assignment expression = 0)

private theorem equations_of_check {assignment : Nat → ZMod babyBearModulus}
    {operations : List (FlatOperation (ZMod babyBearModulus))}
    (checked : equationsCheck assignment operations = true) :
    ∀ expression ∈ FlatOperation.constraints operations,
      Verification.environment assignment expression = 0 := by
  intro expression member
  exact of_decide_eq_true (List.all_eq_true.mp checked expression member)

private theorem machine_equations_00 :
    equationsCheck (machineAssignment 0)
      (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table DynamicCopyLoopProgram.before)) = true := by
  decide +kernel

private theorem machine_equations_01 :
    equationsCheck (machineAssignment 1)
      (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table DynamicCopyLoopProgram.before)) = true := by
  decide +kernel

private theorem machine_equations_02 :
    equationsCheck (machineAssignment 2)
      (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table DynamicCopyLoopProgram.before)) = true := by
  decide +kernel

private theorem machine_equations_03 :
    equationsCheck (machineAssignment 3)
      (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table DynamicCopyLoopProgram.before)) = true := by
  decide +kernel

private theorem machine_equations_04 :
    equationsCheck (machineAssignment 4)
      (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table DynamicCopyLoopProgram.before)) = true := by
  decide +kernel

private theorem machine_equations_05 :
    equationsCheck (machineAssignment 5)
      (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table DynamicCopyLoopProgram.before)) = true := by
  decide +kernel

private theorem machine_equations_06 :
    equationsCheck (machineAssignment 6)
      (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table DynamicCopyLoopProgram.before)) = true := by
  decide +kernel

private theorem machine_equations_07 :
    equationsCheck (machineAssignment 7)
      (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table DynamicCopyLoopProgram.before)) = true := by
  decide +kernel

private theorem machine_equations_08 :
    equationsCheck (machineAssignment 8)
      (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table DynamicCopyLoopProgram.before)) = true := by
  decide +kernel

private theorem machine_equations_09 :
    equationsCheck (machineAssignment 9)
      (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table DynamicCopyLoopProgram.before)) = true := by
  decide +kernel

private theorem machine_equations_10 :
    equationsCheck (machineAssignment 10)
      (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table DynamicCopyLoopProgram.before)) = true := by
  decide +kernel

private theorem machine_equations_11 :
    equationsCheck (machineAssignment 11)
      (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table DynamicCopyLoopProgram.before)) = true := by
  decide +kernel

private theorem machine_equations_12 :
    equationsCheck (machineAssignment 12)
      (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table DynamicCopyLoopProgram.before)) = true := by
  decide +kernel

private theorem machine_equations_13 :
    equationsCheck (machineAssignment 13)
      (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table DynamicCopyLoopProgram.before)) = true := by
  decide +kernel

private theorem machine_equations_14 :
    equationsCheck (machineAssignment 14)
      (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table DynamicCopyLoopProgram.before)) = true := by
  decide +kernel

private theorem machine_equations_15 :
    equationsCheck (machineAssignment 15)
      (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table DynamicCopyLoopProgram.before)) = true := by
  decide +kernel

private theorem machine_equations (index : Fin 16) :
    equationsCheck (machineAssignment index)
      (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table DynamicCopyLoopProgram.before)) = true := by
  fin_cases index
  · exact machine_equations_00
  · exact machine_equations_01
  · exact machine_equations_02
  · exact machine_equations_03
  · exact machine_equations_04
  · exact machine_equations_05
  · exact machine_equations_06
  · exact machine_equations_07
  · exact machine_equations_08
  · exact machine_equations_09
  · exact machine_equations_10
  · exact machine_equations_11
  · exact machine_equations_12
  · exact machine_equations_13
  · exact machine_equations_14
  · exact machine_equations_15

/-- Keep the actual filtered lookup list typed before any index is selected. -/
private noncomputable def machineLookups : List (Lookup (ZMod babyBearModulus)) :=
  FlatOperation.lookups
    (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table DynamicCopyLoopProgram.before))

private theorem machine_lookup_count : machineLookups.length = 18 := by rfl

/-- A witness hint from the actual evaluated query. The subsequent row equality,
not this hint, establishes membership. Modulo only makes the candidate finite. -/
private def machineReferenceIndex (entry : Vector (Expression (ZMod babyBearModulus)) 10)
    (assignment : Nat → ZMod babyBearModulus) : Fin 2097537 :=
  let query := entry.map (Expression.eval (Verification.environment assignment))
  let key : Nat := query[0].val
  let tag : Nat := query[9].val
  let candidate : Nat := if tag = 1 then 524545 + key else if tag = 5 then 655617 + key
    else if tag = 2 then 721153 + key else if tag = 51 then 786689 + key else 0
  ⟨candidate % 2097537, Nat.mod_lt _ (by decide)⟩

private theorem machine_zero_reference :
    UnifiedReduced.Setup.referenceRow DynamicCopyLoopProgram.before 0 =
      #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  change (Verification.shiftBinopRow (0 : Fin 524545)).set 9
    (UnifiedReduced.Setup.binaryTag (Verification.shiftBinopRow (0 : Fin 524545))[9]) = _
  simp only [Verification.shiftBinopRow_eq_reference]
  decide +kernel

/-- The only zero-index simplification uses the existing lossless imported
shift-table characterization, so closed checks never traverse a large data array. -/
private noncomputable def machineCheckRow (index : Fin 2097537) : Vector Nat 10 :=
  if index.val = 0 then #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  else UnifiedReduced.Setup.referenceRow DynamicCopyLoopProgram.before index

private theorem machine_check_row_eq (index : Fin 2097537) :
    machineCheckRow index = UnifiedReduced.Setup.referenceRow DynamicCopyLoopProgram.before index := by
  by_cases zero : index.val = 0
  · have same : index = 0 := Fin.ext zero
    subst index
    change #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0] =
      UnifiedReduced.Setup.referenceRow DynamicCopyLoopProgram.before 0
    exact machine_zero_reference.symm
  · unfold machineCheckRow
    rw [if_neg zero]

private theorem machine_reference_lookup
    (entry : Vector (Expression (ZMod babyBearModulus)) 10)
    (assignment : Nat → ZMod babyBearModulus)
    (same : entry.map (Expression.eval (Verification.environment assignment)) =
      (machineCheckRow (machineReferenceIndex entry assignment)).map
        (fun value : Nat => (value : ZMod babyBearModulus))) :
    (Lookup.mk (UnifiedReduced.Setup.table DynamicCopyLoopProgram.before).toRaw entry).Contains
      (Verification.environment assignment) := by
  change ∃ index : Fin 2097537,
    entry.map (Expression.eval (Verification.environment assignment)) =
      (UnifiedReduced.Setup.row DynamicCopyLoopProgram.before index).map
        (fun value : Nat => (value : ZMod babyBearModulus))
  refine ⟨machineReferenceIndex entry assignment, ?_⟩
  rw [UnifiedReduced.Setup.Proofs.row_eq_reference, ← machine_check_row_eq]
  exact same

private theorem machine_lookup_00 (slot : Fin 18) :
    Lookup.Contains (machineLookups[slot.val]'(by rw [machine_lookup_count]; exact slot.isLt))
      (Verification.environment (machineAssignment 0)) := by
  unfold machineLookups UnifiedReduced.importedConstraints
  dsimp only [FlatOperation.lookups]
  fin_cases slot
  all_goals dsimp only
  all_goals first
    | (apply Verification.range16_contains; decide +kernel)
    | (apply machine_reference_lookup; decide +kernel)

private theorem machine_lookup_01 (slot : Fin 18) :
    Lookup.Contains (machineLookups[slot.val]'(by rw [machine_lookup_count]; exact slot.isLt))
      (Verification.environment (machineAssignment 1)) := by
  unfold machineLookups UnifiedReduced.importedConstraints
  dsimp only [FlatOperation.lookups]
  fin_cases slot
  all_goals dsimp only
  all_goals first
    | (apply Verification.range16_contains; decide +kernel)
    | (apply machine_reference_lookup; decide +kernel)

private theorem machine_lookup_02 (slot : Fin 18) :
    Lookup.Contains (machineLookups[slot.val]'(by rw [machine_lookup_count]; exact slot.isLt))
      (Verification.environment (machineAssignment 2)) := by
  unfold machineLookups UnifiedReduced.importedConstraints
  dsimp only [FlatOperation.lookups]
  fin_cases slot
  all_goals dsimp only
  all_goals first
    | (apply Verification.range16_contains; decide +kernel)
    | (apply machine_reference_lookup; decide +kernel)

private theorem machine_lookup_03 (slot : Fin 18) :
    Lookup.Contains (machineLookups[slot.val]'(by rw [machine_lookup_count]; exact slot.isLt))
      (Verification.environment (machineAssignment 3)) := by
  unfold machineLookups UnifiedReduced.importedConstraints
  dsimp only [FlatOperation.lookups]
  fin_cases slot
  all_goals dsimp only
  all_goals first
    | (apply Verification.range16_contains; decide +kernel)
    | (apply machine_reference_lookup; decide +kernel)

private theorem machine_lookup_04 (slot : Fin 18) :
    Lookup.Contains (machineLookups[slot.val]'(by rw [machine_lookup_count]; exact slot.isLt))
      (Verification.environment (machineAssignment 4)) := by
  unfold machineLookups UnifiedReduced.importedConstraints
  dsimp only [FlatOperation.lookups]
  fin_cases slot
  all_goals dsimp only
  all_goals first
    | (apply Verification.range16_contains; decide +kernel)
    | (apply machine_reference_lookup; decide +kernel)

private theorem machine_lookup_05 (slot : Fin 18) :
    Lookup.Contains (machineLookups[slot.val]'(by rw [machine_lookup_count]; exact slot.isLt))
      (Verification.environment (machineAssignment 5)) := by
  unfold machineLookups UnifiedReduced.importedConstraints
  dsimp only [FlatOperation.lookups]
  fin_cases slot
  all_goals dsimp only
  all_goals first
    | (apply Verification.range16_contains; decide +kernel)
    | (apply machine_reference_lookup; decide +kernel)

private theorem machine_lookup_06 (slot : Fin 18) :
    Lookup.Contains (machineLookups[slot.val]'(by rw [machine_lookup_count]; exact slot.isLt))
      (Verification.environment (machineAssignment 6)) := by
  unfold machineLookups UnifiedReduced.importedConstraints
  dsimp only [FlatOperation.lookups]
  fin_cases slot
  all_goals dsimp only
  all_goals first
    | (apply Verification.range16_contains; decide +kernel)
    | (apply machine_reference_lookup; decide +kernel)

private theorem machine_lookup_07 (slot : Fin 18) :
    Lookup.Contains (machineLookups[slot.val]'(by rw [machine_lookup_count]; exact slot.isLt))
      (Verification.environment (machineAssignment 7)) := by
  unfold machineLookups UnifiedReduced.importedConstraints
  dsimp only [FlatOperation.lookups]
  fin_cases slot
  all_goals dsimp only
  all_goals first
    | (apply Verification.range16_contains; decide +kernel)
    | (apply machine_reference_lookup; decide +kernel)

private theorem machine_lookup_08 (slot : Fin 18) :
    Lookup.Contains (machineLookups[slot.val]'(by rw [machine_lookup_count]; exact slot.isLt))
      (Verification.environment (machineAssignment 8)) := by
  unfold machineLookups UnifiedReduced.importedConstraints
  dsimp only [FlatOperation.lookups]
  fin_cases slot
  all_goals dsimp only
  all_goals first
    | (apply Verification.range16_contains; decide +kernel)
    | (apply machine_reference_lookup; decide +kernel)

private theorem machine_lookup_09 (slot : Fin 18) :
    Lookup.Contains (machineLookups[slot.val]'(by rw [machine_lookup_count]; exact slot.isLt))
      (Verification.environment (machineAssignment 9)) := by
  unfold machineLookups UnifiedReduced.importedConstraints
  dsimp only [FlatOperation.lookups]
  fin_cases slot
  all_goals dsimp only
  all_goals first
    | (apply Verification.range16_contains; decide +kernel)
    | (apply machine_reference_lookup; decide +kernel)

private theorem machine_lookup_10 (slot : Fin 18) :
    Lookup.Contains (machineLookups[slot.val]'(by rw [machine_lookup_count]; exact slot.isLt))
      (Verification.environment (machineAssignment 10)) := by
  unfold machineLookups UnifiedReduced.importedConstraints
  dsimp only [FlatOperation.lookups]
  fin_cases slot
  all_goals dsimp only
  all_goals first
    | (apply Verification.range16_contains; decide +kernel)
    | (apply machine_reference_lookup; decide +kernel)

private theorem machine_lookup_11 (slot : Fin 18) :
    Lookup.Contains (machineLookups[slot.val]'(by rw [machine_lookup_count]; exact slot.isLt))
      (Verification.environment (machineAssignment 11)) := by
  unfold machineLookups UnifiedReduced.importedConstraints
  dsimp only [FlatOperation.lookups]
  fin_cases slot
  all_goals dsimp only
  all_goals first
    | (apply Verification.range16_contains; decide +kernel)
    | (apply machine_reference_lookup; decide +kernel)

private theorem machine_lookup_12 (slot : Fin 18) :
    Lookup.Contains (machineLookups[slot.val]'(by rw [machine_lookup_count]; exact slot.isLt))
      (Verification.environment (machineAssignment 12)) := by
  unfold machineLookups UnifiedReduced.importedConstraints
  dsimp only [FlatOperation.lookups]
  fin_cases slot
  all_goals dsimp only
  all_goals first
    | (apply Verification.range16_contains; decide +kernel)
    | (apply machine_reference_lookup; decide +kernel)

private theorem machine_lookup_13 (slot : Fin 18) :
    Lookup.Contains (machineLookups[slot.val]'(by rw [machine_lookup_count]; exact slot.isLt))
      (Verification.environment (machineAssignment 13)) := by
  unfold machineLookups UnifiedReduced.importedConstraints
  dsimp only [FlatOperation.lookups]
  fin_cases slot
  all_goals dsimp only
  all_goals first
    | (apply Verification.range16_contains; decide +kernel)
    | (apply machine_reference_lookup; decide +kernel)

private theorem machine_lookup_14 (slot : Fin 18) :
    Lookup.Contains (machineLookups[slot.val]'(by rw [machine_lookup_count]; exact slot.isLt))
      (Verification.environment (machineAssignment 14)) := by
  unfold machineLookups UnifiedReduced.importedConstraints
  dsimp only [FlatOperation.lookups]
  fin_cases slot
  all_goals dsimp only
  all_goals first
    | (apply Verification.range16_contains; decide +kernel)
    | (apply machine_reference_lookup; decide +kernel)

private theorem machine_lookup_15 (slot : Fin 18) :
    Lookup.Contains (machineLookups[slot.val]'(by rw [machine_lookup_count]; exact slot.isLt))
      (Verification.environment (machineAssignment 15)) := by
  unfold machineLookups UnifiedReduced.importedConstraints
  dsimp only [FlatOperation.lookups]
  fin_cases slot
  all_goals dsimp only
  all_goals first
    | (apply Verification.range16_contains; decide +kernel)
    | (apply machine_reference_lookup; decide +kernel)

private theorem machine_lookup (index : Fin 16) (slot : Fin 18) :
    Lookup.Contains (machineLookups[slot.val]'(by rw [machine_lookup_count]; exact slot.isLt))
      (Verification.environment (machineAssignment index)) := by
  fin_cases index
  · exact machine_lookup_00 slot
  · exact machine_lookup_01 slot
  · exact machine_lookup_02 slot
  · exact machine_lookup_03 slot
  · exact machine_lookup_04 slot
  · exact machine_lookup_05 slot
  · exact machine_lookup_06 slot
  · exact machine_lookup_07 slot
  · exact machine_lookup_08 slot
  · exact machine_lookup_09 slot
  · exact machine_lookup_10 slot
  · exact machine_lookup_11 slot
  · exact machine_lookup_12 slot
  · exact machine_lookup_13 slot
  · exact machine_lookup_14 slot
  · exact machine_lookup_15 slot

private theorem machine_core (index : Fin 16) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (machineAssignment index))
    (UnifiedReduced.importedConstraints (UnifiedReduced.Setup.table DynamicCopyLoopProgram.before)) := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  refine ⟨equations_of_check (machine_equations index), ?_⟩
  rw [List.forall_mem_iff_forall_getElem]
  intro slot bound
  change slot < machineLookups.length at bound
  have short : slot < 18 := by simpa only [machine_lookup_count] using bound
  change Lookup.Contains (machineLookups[slot]'bound) (Verification.environment (machineAssignment index))
  exact machine_lookup index ⟨slot, short⟩

private theorem machine_clocks (index : Fin 16) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (machineAssignment index))
    UnifiedReduced.importedConstraintsTimestampLookups := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · simp [UnifiedReduced.importedConstraintsTimestampLookups, FlatOperation.constraints]
  · rw [List.forall_mem_iff_forall_getElem]
    intro i bound
    have short : i < 8 := by simpa only [UnifiedReduced.timestamp_count] using bound
    interval_cases i
    all_goals apply Trace.Proofs.range_contains
    all_goals fin_cases index <;> decide +kernel

private def bigintReferenceRow (index : Fin 1390592) : Nat × Nat × Nat :=
  if index.val < 262144 then (index.val / 512, index.val % 512, 22)
  else if index.val < 1310720 then ((index.val - 262144) / 1024, (index.val - 262144) % 1024, 23)
  else if index.val < 1312768 then (index.val - 1310720, 0, 24)
  else if index.val < 1316864 then (index.val - 1312768, 0, 25)
  else if index.val < 1325056 then (index.val - 1316864, 0, 26)
  else (index.val - 1325056, (index.val - 1325056) % 256, 41)

/-- Reuse the established lossless characterization of the actual bigint setup;
this small relation avoids evaluating its large serialized columns per query. -/
private theorem bigint_lookup_relation (entry : Vector (Expression (ZMod babyBearModulus)) 3)
    (env : Environment (ZMod babyBearModulus)) :
    (Lookup.mk Bigint.setupTable.toRaw entry).Contains env ↔
      ∃ i : Fin 1390592, entry.map (Expression.eval env) =
        #v[((bigintReferenceRow i).1 : ZMod babyBearModulus),
          ((bigintReferenceRow i).2.1 : ZMod babyBearModulus),
          ((bigintReferenceRow i).2.2 : ZMod babyBearModulus)] := by
  change (∃ i : Fin 1390592, entry.map (Expression.eval env) =
        #v[((Bigint.setupRow i).1 : ZMod babyBearModulus),
          ((Bigint.setupRow i).2.1 : ZMod babyBearModulus),
          ((Bigint.setupRow i).2.2 : ZMod babyBearModulus)]) ↔ _
  simp only [Bigint.Proofs.setup_row_characterization, bigintReferenceRow]

private theorem worker_equations_0 :
    equationsCheck (workerAssignment 0) (Bigint.importedConstraints Bigint.setupTable) = true := by
  decide +kernel

private theorem worker_equations_1 :
    equationsCheck (workerAssignment 1) (Bigint.importedConstraints Bigint.setupTable) = true := by
  decide +kernel

private def workerLookups : List (Lookup (ZMod babyBearModulus)) :=
  FlatOperation.lookups (Bigint.importedConstraints Bigint.setupTable)

private theorem worker_lookup_count : workerLookups.length = 95 := by rfl

/-- Bounded witness selection from the real bigint query. The complete actual
query-to-row equality below is still mandatory for every fixed lookup. -/
private def workerReferenceIndex (entry : Vector (Expression (ZMod babyBearModulus)) 3)
    (assignment : Nat → ZMod babyBearModulus) : Fin 1390592 :=
  let query := entry.map (Expression.eval (Verification.environment assignment))
  let key : Nat := query[0].val
  let second : Nat := query[1].val
  let tag : Nat := query[2].val
  let candidate : Nat := if tag = 22 then key * 512 + second
    else if tag = 23 then 262144 + key * 1024 + second
    else if tag = 24 then 1310720 + key else if tag = 25 then 1312768 + key
    else if tag = 26 then 1316864 + key else 1325056 + key
  ⟨candidate % 1390592, Nat.mod_lt _ (by decide)⟩

private theorem worker_reference_lookup
    (entry : Vector (Expression (ZMod babyBearModulus)) 3)
    (assignment : Nat → ZMod babyBearModulus)
    (same : entry.map (Expression.eval (Verification.environment assignment)) =
      #v[((bigintReferenceRow (workerReferenceIndex entry assignment)).1 : ZMod babyBearModulus),
        ((bigintReferenceRow (workerReferenceIndex entry assignment)).2.1 : ZMod babyBearModulus),
        ((bigintReferenceRow (workerReferenceIndex entry assignment)).2.2 : ZMod babyBearModulus)]) :
    (Lookup.mk Bigint.setupTable.toRaw entry).Contains (Verification.environment assignment) := by
  rw [bigint_lookup_relation]
  exact ⟨workerReferenceIndex entry assignment, same⟩

private theorem worker_lookup_0 (slot : Fin 95) :
    Lookup.Contains (workerLookups[slot.val]'(by rw [worker_lookup_count]; exact slot.isLt))
      (Verification.environment (workerAssignment 0)) := by
  unfold workerLookups Bigint.importedConstraints
  dsimp only [FlatOperation.lookups]
  fin_cases slot
  all_goals dsimp only
  all_goals first
    | (apply Verification.range16_contains; decide +kernel)
    | (apply Trace.Proofs.range_contains; decide +kernel)
    | (apply worker_reference_lookup; decide +kernel)

private theorem worker_lookup_1 (slot : Fin 95) :
    Lookup.Contains (workerLookups[slot.val]'(by rw [worker_lookup_count]; exact slot.isLt))
      (Verification.environment (workerAssignment 1)) := by
  unfold workerLookups Bigint.importedConstraints
  dsimp only [FlatOperation.lookups]
  fin_cases slot
  all_goals dsimp only
  all_goals first
    | (apply Verification.range16_contains; decide +kernel)
    | (apply Trace.Proofs.range_contains; decide +kernel)
    | (apply worker_reference_lookup; decide +kernel)

private theorem worker_lookup (index : Fin 2) (slot : Fin 95) :
    Lookup.Contains (workerLookups[slot.val]'(by rw [worker_lookup_count]; exact slot.isLt))
      (Verification.environment (workerAssignment index)) := by
  fin_cases index
  · exact worker_lookup_0 slot
  · exact worker_lookup_1 slot

private theorem worker_core (index : Fin 2) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (workerAssignment index)) (Bigint.importedConstraints Bigint.setupTable) := by
  rw [FlatOperation.constraintsHoldFlat_iff_forall_mem]
  constructor
  · apply equations_of_check
    fin_cases index
    · exact worker_equations_0
    · exact worker_equations_1
  · rw [List.forall_mem_iff_forall_getElem]
    intro slot bound
    change slot < workerLookups.length at bound
    have short : slot < 95 := by simpa only [worker_lookup_count] using bound
    change Lookup.Contains (workerLookups[slot]'bound) (Verification.environment (workerAssignment index))
    exact worker_lookup index ⟨slot, short⟩

private theorem worker_clocks (index : Fin 2) : FlatOperation.ConstraintsHoldFlat
    (Verification.environment (workerAssignment index))
    (Bigint.importedConstraintsTimestampLookups (p := babyBearModulus)) := by
  fin_cases index <;> simp [Bigint.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat]
  all_goals repeat' apply And.intro
  all_goals apply Trace.Proofs.range_contains
  all_goals simp [Expression.eval, Verification.environment, workerAssignment]
  all_goals decide +kernel

theorem callers_exact : data.callers =
    [⟨.machine, machineAssignment 7⟩, ⟨.machine, machineAssignment 11⟩] := by rfl

/-- Exact request multiplicity, fullCSR identities, native PC/clock matching,
and all imported machine/worker checks are separate from shared memory matching. -/
theorem checks : UnifiedReduced.Caller.RequestChecks data := by
  constructor
  · intro row member
    change row ∈ machineRows at member
    rcases List.mem_map.mp member with ⟨index, _, rfl⟩
    exact Verification.holds_append (machine_core index) (machine_clocks index)
  · intro row member
    change row ∈ machineRows at member
    rcases List.mem_map.mp member with ⟨index, _, rfl⟩
    fin_cases index <;> decide +kernel
  · change ((data.machine.rows.map Trace.Row.start) ++ [data.machine.terminal]).Perm
      ([data.machine.terminal] ++ data.machine.rows.map Trace.Row.start)
    exact List.perm_append_comm
  · intro row member
    rw [callers_exact] at member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl
    all_goals exact ⟨(0 : Fin 1), by decide +kernel⟩
  · intro row member
    change row ∈ workerRows at member
    rcases List.mem_map.mp member with ⟨index, _, rfl⟩
    exact Verification.holds_append (worker_core index) (worker_clocks index)
  · intro row member
    change row ∈ workerRows at member
    rcases List.mem_map.mp member with ⟨index, _, rfl⟩
    fin_cases index <;> decide +kernel
  · have equal : data.calls = data.fulfillments := by decide +kernel
    unfold Delegation.Requests.Matching
    rw [← equal]
    exact List.perm_append_comm

private theorem ordinary_decoded (index : Fin 16)
    (noncaller : (⟨.machine, machineAssignment index⟩ : Row babyBearModulus UnifiedFamily) ∉ data.callers) :
    (UnifiedReduced.decoderTable DynamicCopyLoopProgram.ordinaryProgram).Contains #[]
      (⟨.machine, machineAssignment index⟩ : Row babyBearModulus UnifiedFamily).decoderQuery := by
  fin_cases index
  all_goals solve
    | exact ⟨(0 : Fin 11), by decide +kernel⟩
    | exact ⟨(1 : Fin 11), by decide +kernel⟩
    | exact ⟨(2 : Fin 11), by decide +kernel⟩
    | exact ⟨(3 : Fin 11), by decide +kernel⟩
    | exact ⟨(4 : Fin 11), by decide +kernel⟩
    | exact ⟨(5 : Fin 11), by decide +kernel⟩
    | exact ⟨(6 : Fin 11), by decide +kernel⟩
    | exact ⟨(7 : Fin 11), by decide +kernel⟩
    | exact ⟨(8 : Fin 11), by decide +kernel⟩
    | exact ⟨(9 : Fin 11), by decide +kernel⟩
    | exact ⟨(10 : Fin 11), by decide +kernel⟩
    | exact False.elim (noncaller (by rw [callers_exact]; simp))

/-- Outright acceptance of the concrete candidate. It supplies no new input
assumption to the general execution theorem and asserts no Sail execution itself. -/
theorem accepted : UnifiedReduced.Caller.MixedMemoryAccepted data DynamicCopyLoopProgram.ordinaryProgram := by
  refine ⟨checks, ?_, memory_matching⟩
  intro row member noncaller
  change row ∈ machineRows at member
  rcases List.mem_map.mp member with ⟨index, _, rfl⟩
  exact ordinary_decoded index noncaller

theorem nativeWitness :
    UnifiedReduced.Caller.MixedMemoryAccepted data DynamicCopyLoopProgram.ordinaryProgram ∧
    UnifiedReduced.Caller.MixedMemoryInputs data DynamicCopyLoopProgram.ordinaryProgram
      DynamicCopyLoopProgram.before [132] [0, 4, 8, 12, 16, 20, 128, 136, 140, 144, 152] cells :=
  ⟨accepted, inputs⟩

/-- The actual physical initialized history derives the current F04 worker-RAM
restriction. It neither broadens the ROM-copy scope nor closes enforcement for
arbitrary native zero-shadow worker witnesses. -/
theorem worker_ram : ExternalBoundary.WorkerRAM.Binding data.workers.rows :=
  UnifiedReduced.Caller.NativeROM.ram_binding_soundness accepted inputs
    (fun address member => (ram_scope address member).1)

end Tests.DynamicCopyLoopNative
