module
public import Human.Compiler.NativePublicSetup
public import Human.Compiler.NativeSetups.Rows

@[expose] public section
namespace Airbender.Compiler.NativeSetups
open Airbender Trace NativeArithmetic

/- The setup fixture program of the CPU setup JSON files as a machine state and a public program, and the statement
   that a CPU setup holds its public generic rows. This module does not read the raw setup data. -/

/-- The initial state of the setup fixture program: PC zero, zero registers, zero RAM, and a ROM that holds the
    words `fixtureWords` in little-endian byte order (ROM byte `address` is byte `address % 4` of word
    `address / 4`). -/
def fixtureInitial : RV.State where
  pc := 0
  regFile := fun _ => 0
  rom := fun address => (fixtureWords (address.toNat / 4) >>> (8 * (address.toNat % 4))).setWidth 8
  mem := fun _ => 0

/-- The public program of the setup fixture in machine profile `config`: the program image of its four ROM words at
    the addresses 0, 4, 8 and 12, made by `rvMachineProgramImage` (the function of `BootInputs.programImage`). The
    image always exists. -/
def fixtureProgram (config : RVMachineConfig) : List RVMachineProgramEntry :=
  (rvMachineProgramImage config fixtureInitial [0, 4, 8, 12]).getD []

/-- The imported setup `data` of CPU circuit `family` holds the public generic rows (lookup group 0) of the setup
    fixture program in machine profile `config` on the complete trace domain: the fixed and ROM rows, the decoder
    rows with their tag, and the padding rows, as `NativePublicSetup.genericRow` defines them. -/
def FixtureRows (family : RVMachineDecoderFamily) (config : RVMachineConfig) (data : Import.Setup.SetupData) : Prop :=
  data.traceLen = (NativeLookups.circuitFor family).trace_len ∧
  ∀ index < data.traceLen,
    NativePublicSetup.genericRow family fixtureInitial (fixtureProgram config) index = importedRows data 0 index

end Airbender.Compiler.NativeSetups
