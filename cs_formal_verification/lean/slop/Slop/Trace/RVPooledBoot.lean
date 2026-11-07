import Human.Helpers.Context.RVPooledBoundary
import Human.Helpers.Core.BabyBearPrime
import Slop.Trace.RVHistory
import Slop.Trace.ROMView
import Slop.Final.Circuits.InitsTeardowns.Theorems

/-! The boot side of the six-family RV claims (`RVPooledBootInputs`): the native seed is the zero boot image of the
    tracked cells (register seeds, then the inits/teardowns `Init` tokens, `InitsTeardowns.standalone_claim`), so every
    tracked cell of the starting state reads 0 (`boot_cells_zero`), and the boot inputs give the RV native inputs. -/

namespace Airbender.Trace.Proofs
open Arithmetic

theorem initialToken_injective {p : Nat} {cell : Cell} {a b : BitVec 32}
    (same : cell.initialToken (p := p) a = cell.initialToken b) : a = b := by
  have pair := (Nat.pair_eq_pair.mp (congrArg MemoryToken.value same))
  have word : Word.ofBitVec a = Word.ofBitVec b := by
    cases ha : Word.ofBitVec a
    cases hb : Word.ofBitVec b
    simp only [Cell.initialToken, ha, hb] at pair
    rw [pair.1, pair.2]
  rw [← Word.ofBitVec_roundtrip a, word, Word.ofBitVec_roundtrip]

/-- A state whose tracked cells read as the zero boot image reads 0 in every tracked cell. -/
theorem rv_image_zero {p : Nat} {s : RV.State} {cells : List Cell}
    (image : initialImageRV (p := p) s cells = some (ROMView.nativeBootImage cells)) :
    ∀ cell ∈ cells, cell.readRV s = some 0 := by
  have reads := rvImage_reads cells _ image
  clear image
  induction cells with
  | nil => simp
  | cons cell rest ih =>
    rcases List.forall₂_cons.mp reads with ⟨⟨value, read, same⟩, tail⟩
    intro other member
    rcases List.mem_cons.mp member with rfl | member
    · rw [read, initialToken_injective same.symm]
    · exact ih tail other member

/-- The boot seed is the zero boot image of the tracked cells: the register seeds, then the instances' `Init` tokens,
    which the inits/teardowns claim makes the zero boot image of their windows. -/
theorem rv_boot_seed {trace : PooledTrace babyBearModulus} {initial : RV.State} {cells : List Cell}
    {program : List RVPooledProgramEntry}
    {inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)}
    {projection : RV.Instr → Option (DecoderData PooledFamily)}
    (inputs : RVPooledBootInputs trace initial cells program inits projection) :
    trace.initialMemory = ROMView.nativeBootImage cells := by
  rw [inputs.seeds, inputs.domain, (InitsTeardowns.standalone_claim.1.bootImage inits inputs.topBits).2]
  simp only [registerSeeds, ROMView.nativeBootImage, List.map_append]

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
