module
public import Human.Helpers.Decoder.RVMachineProgram
public import Human.Helpers.Delegation.RVDecoder
public import Proven.Compiler.ExecutableDecoder
public import Proven.Trace.Machine.Program
public import Mathlib.Tactic.IntervalCases

open Airbender Airbender.Trace

-- The native program projection preserves each ordinary model's complete nine-column query.
example {Kind : Type} (family : Kind → RVMachineDecoderFamily) (entry : RVProgramEntry Kind) :
    ((RVMachineDecoderData.ofOrdinary (family := family) entry.data).row entry.pc).map
      (fun (value : Nat) => (value : ZMod babyBearModulus)) = entry.query := by
  apply Vector.ext
  intro i hi
  interval_cases i <;>
    simp [RVMachineDecoderData.ofOrdinary, RVMachineDecoderData.row,
      RVProgramEntry.query, Arithmetic.Word.ofBitVec, Arithmetic.limbBase]

-- Input metadata is the family projection, with the configured arithmetic family.
example (config : RVMachineConfig) (rd : RV.Reg) :
    rvMachineExtraFields config (.inputRead rd) =
      (NonDeterminism.rvDecoderFields (.inputRead rd)).map
        (RVMachineDecoderData.ofOrdinary (fun _ => config.arithmeticFamily)) := by
  dsimp only [rvMachineExtraFields, NonDeterminism.rvDecoderFields]
  split <;> rfl

example (config : RVMachineConfig) (source : RV.Reg) :
    rvMachineExtraFields config (.inputWrite source) =
      (NonDeterminism.rvDecoderFields (.inputWrite source)).map
        (RVMachineDecoderData.ofOrdinary (fun _ => config.arithmeticFamily)) := rfl

-- The caller row retains the full CSR, which does not fit in an ordinary register field.
example (config : RVMachineConfig) (family : Delegation.Family) :
    rvMachineExtraFields config (.delegate family.rvKind) =
      if config.admitsDelegation family.rvKind then
        (Delegation.Caller.rvDecoderFields (.delegate family.rvKind)).map fun data =>
          { RVMachineDecoderData.ofOrdinary (fun _ => config.arithmeticFamily) data with
            rs2 := family.rvKind.csr.toNat }
      else none := by
  cases family <;> rfl

-- Reduced preprocessing rejects these words before x0 NOP conversion.
example : (RV.decode 0x02208033#32).bind (rvMachineDecoderFields .unrolledReduced) = none := by decide +kernel
example : (RV.decode 0x0220b033#32).bind (rvMachineDecoderFields .unrolledReduced) = none := by decide +kernel
example : (RV.decode 0x0220d033#32).bind (rvMachineDecoderFields .unrolledReduced) = none := by decide +kernel
example : (RV.decode 0x0220f033#32).bind (rvMachineDecoderFields .unrolledReduced) = none := by decide +kernel
example : (RV.decode 0x00008003#32).bind (rvMachineDecoderFields .unrolledReduced) = none := by decide +kernel
example : (RV.decode 0x00009003#32).bind (rvMachineDecoderFields .unrolledReduced) = none := by decide +kernel
example : (RV.decode 0x0000c003#32).bind (rvMachineDecoderFields .unrolledReduced) = none := by decide +kernel
example : (RV.decode 0x0000d003#32).bind (rvMachineDecoderFields .unrolledReduced) = none := by decide +kernel
example : rvMachineDecoderFields .unrolledFullUnsigned (.delegate .blakeG) = none := by decide +kernel

private def interiorUnsupported : RV.State := {
  pc := 0, regFile := fun _ => 0, mem := fun _ => 0
  rom := fun address =>
    BitVec.ofNat 8 ((#[0x13, 0xc0001073, 0x13][address.toNat / 4]?.getD 0) >>>
      (8 * (address.toNat % 4))) }

-- An unsupported interior word leaves a sentinel and retains the next supported word at PC 8.
example : (rvMachineProgramImage .unrolledFullUnsigned interiorUnsupported [0, 4, 8]).map
    (List.map (fun entry => entry.pc.toNat)) = some [0, 8] := by decide +kernel

example : let program := (rvMachineProgramImage .unrolledFullUnsigned interiorUnsupported [0, 4, 8]).getD []
    (rvMachineProgramSlot program 1).isNone ∧
      ((rvMachineProgramSlot program 2).map (fun entry => entry.pc.toNat)) = some 8 := by decide +kernel

-- The executable native payload is the row definition used by the machine targets.
example (initial : RV.State) (family : RVMachineDecoderFamily)
    (program : List RVMachineProgramEntry) (index : Airbender.Compiler.NativeSetupIndex family)
    (inside : index.val - Airbender.Compiler.NativePublicSetup.Metadata.offset family < 1048576)
    (afterFixed : Airbender.Compiler.NativePublicSetup.Metadata.offset family ≤ index.val) :
    Airbender.Compiler.NativePublicSetup.rows initial program family 0 index =
      (Airbender.Compiler.NativePublicSetup.decoderRowNatWith family (rvMachineProgramSlot program)
        (index.val - Airbender.Compiler.NativePublicSetup.Metadata.offset family)).map
          (fun (value : Nat) => (value : Airbender.Compiler.NativeArithmetic.F)) :=
  Airbender.Compiler.NativePublicSetup.rows_decoder_binding initial family program index inside afterFixed

private def zeroWordEntry : RVMachineProgramEntry :=
  ⟨0, 0x00002083, ⟨.pooled .wordMemory, 0, 0, 1, ⟨0, 0⟩, 0, 0⟩⟩

private def zeroHalfEntry : RVMachineProgramEntry :=
  ⟨4, 0x00005083, ⟨.pooled .subwordMemory, 0, 0, 1, ⟨0, 0⟩, 0, 0⟩⟩

private def zeroMaskProgram : List RVMachineProgramEntry := [zeroWordEntry, zeroHalfEntry]

-- LW and LHU retain the native zero mask and satisfy the public setup properties.
example : (RV.decode 0x00002083#32).bind (rvMachineDecoderFields .unrolledFullUnsigned) =
    some zeroWordEntry.data := by kernel_rfl

example : (RV.decode 0x00005083#32).bind (rvMachineDecoderFields .unrolledFullUnsigned) =
    some zeroHalfEntry.data := by kernel_rfl

example (initial : RV.State) : Airbender.Compiler.NativePublicSetup.Bound initial zeroMaskProgram
    (Airbender.Compiler.NativePublicSetup.rows initial zeroMaskProgram) := by
  refine ⟨rfl, by decide +kernel, ?_, ?_⟩
  · intro entry present
    simp [zeroMaskProgram] at present
    rcases present with rfl | rfl <;> decide +kernel
  · intro entry present
    simp [zeroMaskProgram] at present
    rcases present with rfl | rfl <;> decide +kernel
