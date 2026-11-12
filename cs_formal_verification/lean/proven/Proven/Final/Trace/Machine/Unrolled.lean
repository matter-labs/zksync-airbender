module
public import Proven.Trace.Machine.UnrolledRun
public import Proven.Trace.Machine.Boot
public import Proven.Final.Circuits.InitsTeardowns.Theorems

@[expose] public section
namespace Airbender.Trace.Machine
open Airbender.Trace.Machine.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- The full unsigned native machine executes the public program, with its matched standard and split calls. -/
theorem unrolled_full_unsigned : UnrolledFullUnsigned := by
  intro trace workers initial cells program inits boot wordSetup subwordSetup tables noSpecial _ stream accepted
  obtain ⟨addresses, programImage⟩ := boot.programImage
  have clocks := boot_clocks InitsTeardowns.standalone_claim.1 boot
  exact unrolled_realizes (by decide) accepted clocks.initial clocks.aligned boot.image boot.distinct boot.aligned
    programImage wordSetup subwordSetup tables (boot_terminal_bound boot accepted.states) (boot_start boot) noSpecial stream

/-- The reduced native machine executes the public program, with modular operations and matched round calls. -/
theorem unrolled_reduced : UnrolledReduced := by
  intro trace workers initial cells program inits boot wordSetup subwordSetup tables stream accepted
  obtain ⟨addresses, programImage⟩ := boot.programImage
  have clocks := boot_clocks InitsTeardowns.standalone_claim.1 boot
  have noSpecial : NoSpecial5 program := by
    intro entry present decoded
    obtain ⟨_, _, instruction, source, fields⟩ := machine_entry_fetch programImage entry present
    have equal : instruction = .delegate .keccak := Option.some.inj (source.symm.trans decoded)
    subst instruction
    have rejected : rvMachineDecoderFields .unrolledReduced (.delegate .keccak) = none := rfl
    rw [rejected] at fields
    cases fields
  exact unrolled_realizes (by decide) accepted clocks.initial clocks.aligned boot.image boot.distinct boot.aligned
    programImage wordSetup subwordSetup tables (boot_terminal_bound boot accepted.states) (boot_start boot) noSpecial stream

end Airbender.Trace.Machine
