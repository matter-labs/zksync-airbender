module
public import Proven.Trace.Machine.RealizesFromCuts
public import Proven.Trace.Machine.InputIndex
public import Proven.Trace.Machine.InputLift

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Trace.Proofs
set_option warningAsError true

/-- A checked cycle uses the PC and input count at its native boundary cuts. -/
theorem native_cycle_rebase {Kind : Type} [CircuitLayout Kind]
    {initial before after : RV.State} {row : Row babyBearModulus Kind}
    {entry : RVMachineProgramEntry} (index : Nat → Nat) (consumed : Nat)
    (pc : row.start.word.toBitVec = entry.pc)
    (advance : (decodeTimestamp row.assignment row.columns.finalTime).value = row.clock + 4)
    (count : index (row.clock + 4) = index row.clock + consumed)
    (step : ∃ next, RV.step ((before.setPC entry.pc).withInput (initial.input.drop (index row.clock))) = some next ∧
      RV.Same next ((after.setPC row.finish.word.toBitVec).withInput (initial.input.drop (index row.clock + consumed)))) :
    ∃ next, RV.step (nativeView initial index row.start before) = some next ∧
      RV.Same next (nativeView initial index row.finish after) := by
  change ∃ next, RV.step ((before.setPC row.start.word.toBitVec).withInput
    (initial.input.drop (index row.clock))) = some next ∧
    RV.Same next ((after.setPC row.finish.word.toBitVec).withInput
      (initial.input.drop (index (decodeTimestamp row.assignment row.columns.finalTime).value)))
  rw [pc, advance, count]
  exact step

/-- A non-read cycle keeps the independent stream at both boundary cuts. -/
theorem native_nonread_cycle {Kind : Type} [CircuitLayout Kind]
    {initial before after : RV.State} {row : Row babyBearModulus Kind}
    {config : RVMachineConfig} {addresses : List (BitVec 32)} {program : List RVMachineProgramEntry}
    {entry : RVMachineProgramEntry} {instruction : RV.Instr}
    (image : rvMachineProgramImage config initial addresses = some program) (present : entry ∈ program)
    (decoded : RV.decode entry.bits = some instruction) (rom : before.rom = initial.rom)
    (noRead : instruction.readsInput = false) (index : Nat → Nat)
    (pc : row.start.word.toBitVec = entry.pc)
    (advance : (decodeTimestamp row.assignment row.columns.finalTime).value = row.clock + 4)
    (count : index (row.clock + 4) = index row.clock)
    (step : ∃ next, RV.step (before.setPC entry.pc) = some next ∧ RV.Same next (after.setPC row.finish.word.toBitVec)) :
    ∃ next, RV.step (nativeView initial index row.start before) = some next ∧
      RV.Same next (nativeView initial index row.finish after) := by
  apply native_cycle_rebase index 0 pc advance (by simpa using count)
  simpa only [Nat.add_zero] using cycle_step_with_input image present decoded rom noRead row.finish.word.toBitVec step
    (initial.input.drop (index row.clock))

end Airbender.Trace.Machine.Proofs
