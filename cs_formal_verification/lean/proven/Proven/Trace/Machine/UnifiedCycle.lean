module
public import Proven.Trace.Machine.CycleRebase
public import Proven.Trace.Machine.UnifiedOrdinaryCycle
public import Proven.Trace.Machine.UnifiedModularCycle
public import Proven.Trace.Machine.UnifiedInputReadCycle
public import Proven.Trace.Machine.UnifiedInputWriteCycle
public import Proven.Trace.Machine.FieldCases

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Trace.Proofs Delegation
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- The public unified decoder selects a checked CPU step or its matched delegation step. -/
theorem unified_cycle
    {trace : UnifiedTrace babyBearModulus} {workers : WorkerPools babyBearModulus}
    {program : List RVMachineProgramEntry} {initialState before after : RV.State} {cells : List Cell} {addresses : List (BitVec 32)}
    (accepted : UnifiedAcceptance trace workers program)
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (alignedClock : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    (image : initialImageRV initialState cells = some trace.initialMemory)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (programImage : rvMachineProgramImage .unified initialState addresses = some program)
    (setup : trace.rom = UnifiedReduced.Setup.tableRV initialState)
    (tables : workers.standard.setup = modeledSetup Keccak.Controller.rows)
    {row : Row babyBearModulus UnifiedFamily} (member : row ∈ trace.rows)
    {entry : RVMachineProgramEntry} (present : entry ∈ program)
    (query : row.decoderQuery = (entry.data.row entry.pc).map (fun value : Nat => (value : ZMod babyBearModulus)))
    {instruction : RV.Instr} (decoded : RV.decode entry.bits = some instruction)
    (fields : rvMachineDecoderFields .unified instruction = some entry.data)
    (streamPorts : UnifiedStreamPorts trace initialState.input)
    {events : List MemoryAccess} (permutation : events.Perm ((unifiedMemory trace workers).steps.map transferEvent))
    (ordered : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : RVHistory cells (events.filter fun event => decide (row.clock < event.1 ∧ event.1 ≤ row.clock + 4)) before after)
    (rom : before.rom = initialState.rom)
    (delegated : ∀ kind, RV.decode entry.bits = some (.delegate kind) →
      rvMachineDecoderFields .unified (.delegate kind) = some entry.data → row ∈ trace.rows.filter (fun source => decide (UnifiedReduced.Caller.Selected source.assignment)) →
      ∃ next, RV.step (before.setPC entry.pc) = some next ∧ RV.Same next (after.setPC row.finish.word.toBitVec)) :
    ∃ next, RV.step (nativeView initialState (readIndexAt trace.rows Row.clock unifiedIsRead)
      row.start before) = some next ∧
      RV.Same next (nativeView initialState (readIndexAt trace.rows Row.clock unifiedIsRead)
        row.finish after) := by
  let index := readIndexAt trace.rows Row.clock unifiedIsRead
  have clockInputs := state_clock_inputs (by decide) (by decide)
    accepted.constraints accepted.states initial alignedClock
  have advance : (decodeTimestamp row.assignment row.columns.finalTime).value = row.clock + 4 :=
    ClockLaws.advance (by decide) (by decide) trace.rom row (accepted.constraints row member) (clockInputs row member).1
  have unique := state_clocks_unique (by decide) (by decide)
    accepted.constraints accepted.states initial alignedClock
  have count := read_index_cycle trace.rows Row.clock unifiedIsRead unique
    (fun source included => by
      simpa [Row.clock, Timestamp.value, timestampBase, Nat.add_mod, Nat.mul_mod] using (clockInputs source included).2) member
  have pc := machine_query_pc (by decide : limbBase < babyBearModulus) query
  have finish (noRead : instruction.readsInput = false) (nativeRead : unifiedIsRead row = false)
      (step : ∃ next, RV.step (before.setPC entry.pc) = some next ∧ RV.Same next (after.setPC row.finish.word.toBitVec)) :
      ∃ next, RV.step (nativeView initialState index row.start before) = some next ∧
        RV.Same next (nativeView initialState index row.finish after) := by
    apply native_nonread_cycle programImage present decoded rom noRead index pc advance
    · simpa only [nativeRead, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] using count
    · exact step
  rcases machine_fields_cases fields with extra | ⟨_, ordinary, projected, data⟩ | ⟨impossible, _⟩
  · obtain ⟨tag, w⟩ := row
    cases tag
    have core := Verification.holds_of_sublist (accepted.constraints _ member)
      (List.sublist_append_left (UnifiedReduced.importedConstraints trace.rom) UnifiedReduced.importedConstraintsTimestampLookups)
    have flags := unified_extra_flags core extra query
    cases instruction <;> simp only [rvMachineExtraFields] at extra
    all_goals try contradiction
    case delegate kind =>
      have selected : UnifiedReduced.Caller.Selected w := of_decide_eq_true (by simpa only [isCallerInstruction] using flags.1)
      have called : (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily) ∈ trace.rows.filter (fun source => decide (UnifiedReduced.Caller.Selected source.assignment)) := by
        apply List.mem_filter.mpr
        exact ⟨member, decide_eq_true selected⟩
      apply finish rfl (by simpa only [RV.Instr.readsInput] using flags.2)
      exact delegated kind decoded fields called
    case inputRead rd =>
      apply native_cycle_rebase index 1 pc advance
      · simpa only [flags.2, RV.Instr.readsInput, ↓reduceIte] using count
      · exact unified_input_read_cycle accepted initial alignedClock image aligned programImage tables member present rd extra decoded streamPorts query permutation ordered history rom
    case inputWrite source =>
      apply finish rfl (by simpa only [RV.Instr.readsInput] using flags.2)
      exact unified_input_write_cycle accepted initial alignedClock image aligned programImage tables member present source extra decoded query permutation ordered history rom
    case mop op rd rs1 rs2 =>
      apply finish rfl (by simpa only [RV.Instr.readsInput] using flags.2)
      by_cases zero : rd = 0
      · subst rd
        have data : entry.data = RVMachineDecoderData.ofOrdinary (family := fun _ => .unified)
            UnifiedReduced.rvNopFields := (extra_mop_zero_data extra).trans (unified_arithmetic_view rvNopData)
        have projected : UnifiedReduced.rvDecoderFields (.mop op 0 rs1 rs2) = some UnifiedReduced.rvNopFields := rfl
        exact unified_ordinary_cycle accepted initial alignedClock image aligned programImage setup tables member present
          projected data query decoded permutation ordered history rom
      · cases op
        case triAdd =>
          split at extra
          · rename_i equal
            exact False.elim (zero equal)
          · simp only [rvModularMask, Option.map_none] at extra
            cases extra
        case add =>
          exact unified_modular_cycle accepted initial alignedClock image aligned programImage tables member present .add rs1 rs2 rd zero extra decoded query permutation ordered history rom
        case sub =>
          exact unified_modular_cycle accepted initial alignedClock image aligned programImage tables member present .sub rs1 rs2 rd zero extra decoded query permutation ordered history rom
        case mul =>
          exact unified_modular_cycle accepted initial alignedClock image aligned programImage tables member present .mul rs1 rs2 rd zero extra decoded query permutation ordered history rom
        case fma =>
          exact unified_modular_cycle accepted initial alignedClock image aligned programImage tables member present .fma rs1 rs2 rd zero extra decoded query permutation ordered history rom
  · obtain ⟨tag, w⟩ := row
    cases tag
    have core := Verification.holds_of_sublist (accepted.constraints _ member)
      (List.sublist_append_left (UnifiedReduced.importedConstraints trace.rom) UnifiedReduced.importedConstraintsTimestampLookups)
    have flags := unified_ordinary_flags core projected data query
    apply finish (unified_ordinary_no_read projected) flags.2
    exact unified_ordinary_cycle accepted initial alignedClock image aligned programImage setup tables member present
      projected data query decoded permutation ordered history rom
  · exact False.elim (impossible rfl)

end Airbender.Trace.Machine.Proofs
