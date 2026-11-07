import Slop.Trace.RVPooled.Row
import Slop.Trace.RVPooledBoot
import Slop.Trace.RVRealizes
import Slop.Trace.RVPooledLaws
import Slop.Trace.RVZero

/-! The six-family claim over our spec (`RVPooledNativeSoundnessClaim`): the boot inputs give the RV native inputs, the
    pooled laws give the x0 law and the read bounds, every row takes one `RV.step` (`rv_pooled_row_step`), and the
    generic composition (`rv_realizes`) gives `RVRealizes`. -/

namespace Airbender.Trace.Proofs
open Arithmetic

/-- Every row of an accepted RV-decoded pooled trace takes one `RV.step` (standard table). -/
theorem rv_pooled_row_steps (laws : RVPooledLaws) {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : PooledTrace p} {initial : RV.State} {cells : List Cell}
    {program : List RVPooledProgramEntry}
    (native : RVNativeInputs rvPooledDecoderFields trace initial cells program)
    (wordTable : trace.rom.wordMemory = ROM.table cells (romImageRV initial cells))
    (subwordTable : trace.rom.subwordMemory = Verification.subwordTable (ROM.wordsRV initial))
    (terminalPC : trace.terminal.word.Bounded) (accepted : Accepted trace)
    (decoded : RVPooledDecoded trace program) : RVRowSteps trace initial cells := by
  have limbSize : limbBase < p := by dsimp [limbBase]; omega
  obtain ⟨addresses, programImage⟩ := native.programImage
  have bounds := (laws.valueBounds (by omega) inverse accepted native.clocks native.image wordTable subwordTable
    programImage decoded).1
  have finishBounds := JumpBranchSlt.Proofs.rv_pooled_finish_bounds limbSize accepted decoded terminalPC
  intro row member before after position history
  obtain ⟨entry, i, decodes, fields, step, facts⟩ := rv_pooled_row_facts limbSize programImage accepted decoded
    bounds finishBounds native.aligned wordTable subwordTable member position history
  obtain ⟨next, exec, same⟩ := rv_pooled_row_step hp inverse facts fields decodes
  exact ⟨next, step.trans exec, same⟩

/-- `RVPooledNativeSoundnessClaim` for any field, given the zero seed of the tracked cells. -/
theorem rv_pooled_trace_execution (laws : RVPooledLaws) {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : PooledTrace p} {initial : RV.State} {cells : List Cell}
    {program : List RVPooledProgramEntry}
    {inits : List (InitsTeardowns.Witness p InitsTeardowns.importedLayout)}
    (inputs : RVPooledBootInputs trace initial cells program inits)
    (seed : trace.initialMemory = ROMView.nativeBootImage cells)
    (accepted : Accepted trace) (decoded : RVPooledDecoded trace program) :
    RVRealizes trace initial cells := by
  haveI : ClockLaws PooledFamily p := laws.clockLaws
  have clockSize : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  have native := inputs.native (by omega) seed
  obtain ⟨addresses, programImage⟩ := inputs.programImage
  have zero := RVZero.rv_zero_writes_of_preserving clockSize inverse accepted native.clocks inputs.image
    (laws.zeroPreserving (by omega) accepted programImage decoded)
  exact rv_realizes clockSize inverse accepted native.clocks inputs.image inputs.distinct inputs.aligned zero
    inputs.start (rv_pooled_row_steps laws hp inverse native inputs.wordTable inputs.subwordSetup
      inputs.terminalPC accepted decoded)

end Airbender.Trace.Proofs
