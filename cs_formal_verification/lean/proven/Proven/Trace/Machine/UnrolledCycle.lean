module
public import Proven.Trace.Machine.CycleRebase
public import Proven.Trace.Machine.UnrolledOrdinaryCycle
public import Proven.Trace.Machine.UnrolledModularCycles
public import Proven.Trace.Machine.UnrolledInputReadCycle
public import Proven.Trace.Machine.UnrolledInputWriteCycle
public import Proven.Trace.Machine.FieldCases

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Trace.Proofs Delegation
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- The ordinary pooled decoder rejects input reads. -/
theorem pooled_ordinary_no_read {instruction : RV.Instr} {data : DecoderData PooledFamily}
    (fields : rvPooledDecoderFields instruction = some data) : instruction.readsInput = false := by
  cases instruction <;> try rfl
  case inputRead rd =>
    have rejected : rvPooledDecoderFields (.inputRead rd) = none := rfl
    rw [rejected] at fields
    cases fields

/-- The public unrolled decoder selects a checked CPU step or its matched delegation step. -/
theorem unrolled_cycle {config : RVMachineConfig} (unrolled : config ≠ .unified)
    {trace : PooledTrace babyBearModulus} {workers : WorkerPools babyBearModulus}
    {program : List RVMachineProgramEntry} {initialState before after : RV.State} {cells : List Cell} {addresses : List (BitVec 32)}
    (accepted : UnrolledAcceptance trace workers program)
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (alignedClock : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    (image : initialImageRV initialState cells = some trace.initialMemory)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (programImage : rvMachineProgramImage config initialState addresses = some program)
    (wordSetup : trace.rom.wordMemory = ROM.table cells (romImageRV initialState cells))
    (subwordSetup : trace.rom.subwordMemory = Verification.subwordTable (ROM.wordsRV initialState))
    (tables : workers.standard.setup = modeledSetup Keccak.Controller.rows) (terminal : trace.terminal.word.Bounded)
    {row : Row babyBearModulus PooledFamily} (member : row ∈ trace.rows)
    {entry : RVMachineProgramEntry} (present : entry ∈ program)
    (family : entry.data.family = .pooled row.family)
    (query : row.decoderQuery = (entry.data.row entry.pc).map (fun value : Nat => (value : ZMod babyBearModulus)))
    {instruction : RV.Instr} (decoded : RV.decode entry.bits = some instruction)
    (fields : rvMachineDecoderFields config instruction = some entry.data)
    (streamPorts : NonDeterminism.Pooled.StreamPorts trace initialState.input)
    {events : List MemoryAccess} (permutation : events.Perm ((unrolledMemory trace workers).steps.map transferEvent))
    (ordered : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : RVHistory cells (events.filter fun event => decide (row.clock < event.1 ∧ event.1 ≤ row.clock + 4)) before after)
    (rom : before.rom = initialState.rom)
    (delegated : ∀ kind, RV.decode entry.bits = some (.delegate kind) →
      rvMachineDecoderFields config (.delegate kind) = some entry.data → row ∈ unrolledCallers trace →
      ∃ next, RV.step (before.setPC entry.pc) = some next ∧ RV.Same next (after.setPC row.finish.word.toBitVec)) :
    ∃ next, RV.step (nativeView initialState (readIndexAt trace.rows Row.clock NonDeterminism.Pooled.isRead)
      row.start before) = some next ∧
      RV.Same next (nativeView initialState (readIndexAt trace.rows Row.clock NonDeterminism.Pooled.isRead)
        row.finish after) := by
  let index := readIndexAt trace.rows Row.clock NonDeterminism.Pooled.isRead
  have clockInputs := state_clock_inputs (by decide) (by decide)
    accepted.constraints accepted.states initial alignedClock
  have advance : (decodeTimestamp row.assignment row.columns.finalTime).value = row.clock + 4 :=
    ClockLaws.advance (by decide) (by decide) trace.rom row (accepted.constraints row member) (clockInputs row member).1
  have unique := state_clocks_unique (by decide) (by decide)
    accepted.constraints accepted.states initial alignedClock
  have count := read_index_cycle trace.rows Row.clock NonDeterminism.Pooled.isRead unique
    (fun source included => by
      simpa [Row.clock, Timestamp.value, timestampBase, Nat.add_mod, Nat.mul_mod] using (clockInputs source included).2) member
  have pc := machine_query_pc (by decide : limbBase < babyBearModulus) query
  have finish (noRead : instruction.readsInput = false) (nativeRead : NonDeterminism.Pooled.isRead row = false)
      (step : ∃ next, RV.step (before.setPC entry.pc) = some next ∧ RV.Same next (after.setPC row.finish.word.toBitVec)) :
      ∃ next, RV.step (nativeView initialState index row.start before) = some next ∧
        RV.Same next (nativeView initialState index row.finish after) := by
    apply native_nonread_cycle programImage present decoded rom noRead index pc advance
    · simpa only [nativeRead, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] using count
    · exact step
  rcases machine_fields_cases fields with extra | ⟨unified, _⟩ | ⟨_, ordinary, projected, data⟩
  · have rowFamily : row.family = .addSub := RVMachineDecoderFamily.pooled.inj
      (family.symm.trans ((extra_family extra).trans (unrolled_arithmetic_family unrolled)))
    obtain ⟨tag, w⟩ := row
    change tag = .addSub at rowFamily
    subst tag
    have core := Verification.holds_of_sublist (accepted.constraints _ member)
      (List.sublist_append_left AddSub.importedConstraints AddSub.importedConstraintsTimestampLookups)
    have flags := unrolled_extra_flags core extra query
    cases instruction <;> simp only [rvMachineExtraFields] at extra
    all_goals try contradiction
    case delegate kind =>
      have selected : Requests.Selected w := of_decide_eq_true (by simpa only [isCallerInstruction] using flags.1)
      have called : (⟨.addSub, w⟩ : Row babyBearModulus PooledFamily) ∈ unrolledCallers trace := by
        apply List.mem_filter.mpr
        exact ⟨member, by simp [selected]⟩
      apply finish rfl (by simpa only [RV.Instr.readsInput] using flags.2)
      exact delegated kind decoded fields called
    case inputRead rd =>
      apply native_cycle_rebase index 1 pc advance
      · simpa only [flags.2, RV.Instr.readsInput, ↓reduceIte] using count
      · exact unrolled_input_read_cycle unrolled accepted initial alignedClock image aligned programImage wordSetup
          subwordSetup tables terminal member present rd extra decoded streamPorts query permutation ordered history rom
    case inputWrite source =>
      apply finish rfl (by simpa only [RV.Instr.readsInput] using flags.2)
      exact unrolled_input_write_cycle unrolled accepted initial alignedClock image aligned programImage wordSetup
        subwordSetup tables terminal member present source extra decoded query permutation ordered history rom
    case mop op rd rs1 rs2 =>
      apply finish rfl (by simpa only [RV.Instr.readsInput] using flags.2)
      by_cases zero : rd = 0
      · subst rd
        exact unrolled_mop_zero_cycle unrolled accepted initial alignedClock image aligned programImage wordSetup
          subwordSetup tables terminal member present op rs1 rs2 extra decoded query permutation ordered history rom
      · cases op
        case triAdd =>
          split at extra
          · rename_i equal
            exact False.elim (zero equal)
          · simp only [rvModularMask, Option.map_none] at extra
            cases extra
        case add =>
          exact unrolled_modular_cycle unrolled accepted initial alignedClock image aligned programImage wordSetup
            subwordSetup tables terminal member present .add rs1 rs2 rd zero extra decoded query permutation ordered history rom
        case sub =>
          exact unrolled_modular_cycle unrolled accepted initial alignedClock image aligned programImage wordSetup
            subwordSetup tables terminal member present .sub rs1 rs2 rd zero extra decoded query permutation ordered history rom
        case mul =>
          exact unrolled_modular_cycle unrolled accepted initial alignedClock image aligned programImage wordSetup
            subwordSetup tables terminal member present .mul rs1 rs2 rd zero extra decoded query permutation ordered history rom
        case fma =>
          exact unrolled_modular_cycle unrolled accepted initial alignedClock image aligned programImage wordSetup
            subwordSetup tables terminal member present .fma rs1 rs2 rd zero extra decoded query permutation ordered history rom
  · exact False.elim (unrolled unified)
  · have flags := unrolled_ordinary_flags (accepted.constraints row member) projected data family query
    apply finish (pooled_ordinary_no_read projected) flags.2
    exact unrolled_ordinary_cycle unrolled accepted initial alignedClock image aligned programImage wordSetup
      subwordSetup tables terminal member present projected data family query decoded permutation ordered history rom

end Airbender.Trace.Machine.Proofs
