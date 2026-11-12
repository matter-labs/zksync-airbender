module
public import Human.Helpers.Context.RVPooledBoundary
public import Human.Helpers.Core.BabyBearPrime
public import Proven.Trace.RVBootSeed
public import Proven.Trace.ROMView
public import Proven.Final.Circuits.InitsTeardowns.Theorems

@[expose] public section

/-! The boot side of the six-family RV claims (`RVPooledBootInputs`): the native seed is the zero boot image of the
    tracked cells (register seeds, then the inits/teardowns `Init` tokens, `InitsTeardowns.standalone_claim`), so every
    tracked cell of the starting state reads 0 (`boot_cells_zero`), and the boot inputs give the RV native inputs. -/

namespace Airbender.Trace.Proofs
open Arithmetic

/-- The boot seed is the zero boot image of the tracked cells: the register seeds, then the instances' `Init` tokens,
    which the inits/teardowns claim makes the zero boot image of their windows. -/
theorem rv_boot_seed {trace : PooledTrace babyBearModulus} {initial : RV.State} {cells : List Cell}
    {program : List RVPooledProgramEntry}
    {inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)}
    {projection : RV.Instr → Option (DecoderData PooledFamily)}
    (inputs : RVPooledBootInputs trace initial cells program inits projection) :
    trace.initialMemory = ROMView.nativeBootImage cells :=
  boot_seed_image InitsTeardowns.standalone_claim.1 inputs.topBits inputs.seeds inputs.domain

/-- `BootRamZeroClaim`, proved: every tracked RAM cell of the starting state reads 0. -/
theorem boot_ram_zero {trace : PooledTrace babyBearModulus} {initial : RV.State} {cells : List Cell}
    {program : List RVPooledProgramEntry}
    {inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)}
    {projection : RV.Instr → Option (DecoderData PooledFamily)}
    (inputs : RVPooledBootInputs trace initial cells program inits projection) :
    ∀ address, Cell.ram address ∈ cells → (Cell.ram address).readRV initial = some 0 := by
  intro address member
  have image := inputs.image
  rw [rv_boot_seed inputs] at image
  exact rv_image_zero image _ member

/-- The boot inputs with a zero seed give the RV native inputs (clocks from the zero seed and the boundary). -/
theorem _root_.Airbender.Trace.RVPooledBootInputs.native {p : Nat} [Fact p.Prime] (hp : 4 < p) {trace : PooledTrace p}
    {initial : RV.State} {cells : List Cell} {program : List RVPooledProgramEntry}
    {inits : List (InitsTeardowns.Witness p InitsTeardowns.importedLayout)}
    {projection : RV.Instr → Option (DecoderData PooledFamily)}
    (inputs : RVPooledBootInputs trace initial cells program inits projection)
    (seed : trace.initialMemory = ROMView.nativeBootImage cells) :
    RVNativeInputs projection trace initial cells program where
  distinct := inputs.distinct
  aligned := inputs.aligned
  image := inputs.image
  initialPC := ⟨(4, 0), by rw [inputs.initialBoundary, initialStateRV, inputs.pc]⟩
  programImage := inputs.programImage
  clocks := ROMView.native_clocks hp seed inputs.initialBoundary

/-- The starting PC is the trace's initial PC. -/
theorem _root_.Airbender.Trace.RVPooledBootInputs.start {p : Nat} [Fact p.Prime] {trace : PooledTrace p}
    {initial : RV.State} {cells : List Cell} {program : List RVPooledProgramEntry}
    {inits : List (InitsTeardowns.Witness p InitsTeardowns.importedLayout)}
    {projection : RV.Instr → Option (DecoderData PooledFamily)}
    (inputs : RVPooledBootInputs trace initial cells program inits projection) :
    initial.pc = trace.initial.word.toBitVec := by
  rw [inputs.initialBoundary, inputs.pc]
  simp [PCState.boundary, PCState.encode, PCState.State.word, Word.toBitVec, Word.value]

end Airbender.Trace.Proofs
