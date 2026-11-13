module
public import Human.Helpers.Decoder.RVExternalInput
public import Human.Helpers.UnifiedReduced.RVProgram

@[expose] public section

namespace Airbender.Trace
open Arithmetic

/-- The three production setup profiles. -/
inductive RVMachineConfig where
  | unrolledFullUnsigned | unrolledReduced | unified
  deriving DecidableEq

/-- The circuit selected by a public native decoder entry. -/
inductive RVMachineDecoderFamily where
  | pooled (family : PooledFamily)
  | unified
  deriving DecidableEq

/-- Native decoder metadata. The second source can hold a full CSR request identifier. -/
structure RVMachineDecoderData where
  /-- The selected CPU circuit. Worker rows have separate request records. -/
  family : RVMachineDecoderFamily
  /-- The first source register number. -/
  rs1 : Nat
  /-- The second source register number or full CSR request identifier. -/
  rs2 : Nat
  /-- The architectural destination register number. -/
  rd : Nat
  /-- The native immediate limbs. -/
  immediate : Word
  /-- The packed selector bits. -/
  mask : Nat
  /-- The selected operation tag. -/
  funct3 : Nat := 0

/-- Preserve every field of an ordinary decoder entry. -/
def RVMachineDecoderData.ofOrdinary (family : Kind → RVMachineDecoderFamily)
    (data : DecoderData Kind) : RVMachineDecoderData :=
  ⟨family data.family, data.rs1.toNat, data.rs2.toNat, data.rd.toNat,
    data.immediate, data.mask, data.funct3⟩

/-- The complete native row at a public instruction address. -/
def RVMachineDecoderData.row (pc : BitVec 32) (data : RVMachineDecoderData) : Vector Nat 9 :=
  #v[pc.toNat % limbBase, pc.toNat / limbBase, data.rs1, data.rs2, data.rd,
    data.immediate.lo, data.immediate.hi, data.funct3, data.mask]

/-- The request families selected by production preprocessing. Special5 is excluded separately by machine targets. -/
def RVMachineConfig.admitsDelegation (config : RVMachineConfig) : RV.DelegationKind → Bool
  | .blakeRound => true
  | .blakeG | .bigint | .keccak => config != .unrolledReduced
  | .keccakThetaRho | .keccakParity | .keccakChi5 => config == .unrolledFullUnsigned

def RVMachineConfig.arithmeticFamily (config : RVMachineConfig) : RVMachineDecoderFamily :=
  if config == .unified then .unified else .pooled .addSub

def rvModularMask : RV.FieldOp → Option Nat
  | .add => some 8
  | .sub => some 16
  | .mul => some 32
  | .fma => some 64
  | .triAdd => none

/-- Public decoder fields for modular operations, input reads and delegation requests. -/
def rvMachineExtraFields (config : RVMachineConfig) : RV.Instr → Option RVMachineDecoderData
  | .delegate kind =>
    if config.admitsDelegation kind then
      some ⟨config.arithmeticFamily, 0, kind.csr.toNat, 0, ⟨0, 0⟩, 128, 0⟩
    else none
  | .inputRead rd =>
    if rd = 0 then none else
      some ⟨config.arithmeticFamily, 0, 0, rd.toNat, ⟨0, 0⟩, 256, 0⟩
  | .inputWrite _ => some ⟨config.arithmeticFamily, 0, 0, 0, ⟨0, 0⟩, 1, 0⟩
  | .mop op rd rs1 rs2 =>
    if rd = 0 then some ⟨config.arithmeticFamily, 0, 0, 0, ⟨0, 0⟩, 1, 0⟩ else
      (rvModularMask op).map fun mask =>
        ⟨config.arithmeticFamily, rs1.toNat, rs2.toNat, rd.toNat, ⟨0, 0⟩, mask, 0⟩
  | _ => none

/-- The native public-program projection reuses the reviewed ordinary family projections. -/
def rvMachineDecoderFields (config : RVMachineConfig) (instruction : RV.Instr) :
    Option RVMachineDecoderData :=
  rvMachineExtraFields config instruction <|>
    if config == .unified then
      (UnifiedReduced.rvDecoderFields instruction).map
        (RVMachineDecoderData.ofOrdinary (family := fun _ => .unified))
    else
      ((rvPooledDecoderFields instruction).filter fun data =>
        config == .unrolledFullUnsigned ||
          (data.family != .mulDiv && data.family != .subwordMemory)).map
        (RVMachineDecoderData.ofOrdinary (family := RVMachineDecoderFamily.pooled))

/-- A public program entry contains ROM bytes and their native decoder metadata. -/
structure RVMachineProgramEntry where
  /-- The public instruction address. -/
  pc : BitVec 32
  /-- The four public ROM bytes. -/
  bits : BitVec 32
  /-- The metadata computed from those bytes. -/
  data : RVMachineDecoderData

/-- Read aligned public ROM words through the same fetch boundary as `rvProgramImageWith`. -/
def rvMachineProgramImage (config : RVMachineConfig) (initial : RV.State)
    (addresses : List (BitVec 32)) : Option (List RVMachineProgramEntry) :=
  addresses.mapM fun pc => do
    if ¬(pc.toNat < RV.ROM_END ∧ pc.toNat % 4 = 0) then none else
      let bits := RV.read initial.rom pc 4
      let instruction ← RV.decode bits
      let data ← rvMachineDecoderFields config instruction
      pure ⟨pc, bits, data⟩

end Airbender.Trace
