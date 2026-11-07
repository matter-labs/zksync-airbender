import Human.Trace.Families.AddSub.RVTheorems
import Slop.AddSub.RVTraceExecution
import Slop.WordMemory.RVTraceExecution
import Slop.Trace.Family.History
import Slop.Trace.Family.Values
import Slop.Trace.RVFamilySelectors
import Slop.Trace.RVZeroRows
import Slop.Trace.RVValues
import Slop.Trace.ROMView
import Slop.Trace.RVBootSeed
import Slop.Final.Circuits.InitsTeardowns.Theorems
import Slop.UnifiedReduced.RV.Execution

/-! The ADD/SUB + word-memory trace claims on the RV route (`RVAirbenderSoundnessClaim`, `RVNativeBootSoundnessClaim`):
    no Sail state, interpreter, `Configured` or `OrdinaryWordAddress` fact. Rows step by family
    (`AddSub.Proofs.rv_row_step`, `WordMemory.Proofs.rv_row_step`); x0 is preserved (`row_zero_write_from_reads`);
    read values are bounded (`row_write_source` with the ROM-image word table); the composition is
    `rv_family_realizes`. Native boot: the seeds are the inits/teardowns
    circuit's zero boot image (`boot_seed_image`), and the boot clocks are `ROMView.native_clocks`. -/

namespace Airbender.Trace.Proofs
open Arithmetic

/-- Every row of an accepted RV-decoded two-family trace preserves x0. -/
theorem rv_family_zero_preserving {p : Nat} [Fact p.Prime] (hp : 196608 < p)
    {trace : Data p} (accepted : Accepted trace) {initial : RV.State} {addresses : List (BitVec 32)}
    {program : List RVProgramEntry} (image : rvProgramImageWith rvDecoderFields initial addresses = some program)
    (decoded : RVDecoded trace program) : ZeroPreserving trace := by
  have limbField : limbBase < p := by dsimp [limbBase]; omega
  intro row member
  obtain ⟨entry, present, family, query⟩ := rv_decoder_member (decoded row member)
  obtain ⟨_, _, i, _, fields⟩ := rvProgram_entry_fetch image entry present
  have mask : entry.data.mask < 512 := (rvStandardDecoderRules.bounds _ _ fields).2
  have fetch : RVZero.RVFetched row rvDecoderFields :=
    ⟨entry, i, fields, family, query,
      rv_row_query_selectors_of_bound limbField trace.rom (accepted.constraints _ member) mask query⟩
  exact RVZero.row_zero_write_from_reads rvStandardDecoderRules hp row trace.rom (accepted.constraints _ member)
    fetch

/-- Every read of an accepted two-family trace seeded by an RV image, with the ROM-image word table, is a bounded
    word. -/
theorem rv_family_read_bounds {p : Nat} [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p} (accepted : Accepted trace)
    (clocks : ClockBoundary trace) {initial : RV.State} {cells : List Cell}
    (image : initialImageRV initial cells = some trace.initialMemory)
    (rom : trace.rom = ROM.table cells (romImageRV initial cells)) :
    ∀ row ∈ trace.rows, ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded := by
  have limbField : limbBase < p := by dsimp [limbBase, timestampBase] at hp ⊢; omega
  have sources : WriteSources trace := fun row member port present =>
    row_write_source row trace.rom (accepted.constraints row member)
      (fun query h inactive => RVValues.rv_rom_disabled (by dsimp [timestampBase] at hp; omega)
        (by rwa [rom] at h) inactive)
      (fun query h => RVValues.rv_rom_bounds limbField (by rwa [rom] at h)) port present
  exact read_bounds_of_sources hp inverse accepted clocks (RVValues.rv_image_bounds image) sources

/-- `RVAirbenderSoundnessClaim` for any field with `536870912 ≤ p`. -/
theorem rv_family_execution {p : Nat} [Fact p.Prime] (hp : 536870912 ≤ p)
    (inverse : (-3840 : ZMod p) * 524288 = 1)
    {trace : Data p} {initial : RV.State} {cells : List Cell} {program : List RVProgramEntry}
    (inputs : RVExecutionBoundary trace initial cells program)
    (accepted : Accepted trace) (decoded : RVDecoded trace program) :
    RVRealizes trace initial cells := by
  have clockSize : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  have limbSize : limbBase < p := by dsimp [limbBase]; omega
  obtain ⟨addresses, image⟩ := inputs.programImage
  have bounds := rv_family_read_bounds clockSize inverse accepted inputs.clocks inputs.image inputs.rom
  refine rv_family_realizes clockSize inverse accepted inputs.toRVNativeInputs
    (rv_family_zero_preserving (by omega) accepted image decoded)
    (rv_family_row_steps limbSize image (fun row entry => entry.data.family = row.family)
      (fun row member => by
        obtain ⟨entry, present, family, query⟩ := rv_decoder_member (decoded row member)
        exact ⟨entry, present, family, query⟩) ?_)
  intro row member entry _ family query i decodes fields _ before after pc romSame history
  have active : row.assignment 4 = 1 := by
    cases row with
    | mk kind w =>
      cases kind <;> simpa [Row.columns, CircuitLayout.columns, AddSub.importedConstraintsTraceColumns,
        WordMemory.importedConstraintsTraceColumns] using accepted.active _ member
  obtain ⟨kind, w⟩ := row
  cases kind
  · -- ADD/SUB-family rows.
    have read (k : Fin 2) := bounds _ member AddSub.importedConstraintsMemoryPorts[k]
      (by change AddSub.importedConstraintsMemoryPorts[k] ∈ AddSub.importedConstraintsMemoryPorts
          fin_cases k <;> simp [AddSub.importedConstraintsMemoryPorts])
    have leftBound : (Word.mk (w 25).val (w 26).val).Bounded := by
      simpa [read_word, AddSub.importedConstraintsMemoryPorts] using read 0
    have rightBound : (Word.mk (w 29).val (w 30).val).Bounded := by
      simpa [read_word, AddSub.importedConstraintsMemoryPorts] using read 1
    exact AddSub.Proofs.rv_row_step hp inverse (accepted.constraints _ member) active family query decodes fields
      leftBound rightBound trace.memoryEpoch pc history
  · -- Word-memory rows.
    have core := Verification.holds_of_sublist (accepted.constraints _ member)
      (List.sublist_append_left (WordMemory.importedConstraints trace.rom)
        WordMemory.importedConstraintsTimestampLookups)
    rw [inputs.rom] at core
    have source := bounds _ member WordMemory.importedConstraintsMemoryPorts[0]
      (by change WordMemory.importedConstraintsMemoryPorts[0] ∈ WordMemory.importedConstraintsMemoryPorts
          simp [WordMemory.importedConstraintsMemoryPorts])
    have sourceBound : (Word.mk (w 17).val (w 18).val).Bounded := by
      simpa [read_word, WordMemory.importedConstraintsMemoryPorts] using source
    exact WordMemory.Proofs.rv_row_step hp inverse core active family query decodes fields sourceBound
      inputs.aligned trace.memoryEpoch pc romSame history

/-- Native boot gives the public RV inputs: the seeds are the zero boot image of the inits/teardowns windows and the
    registers (`boot_seed_image`), the boot PC and clock form the native starting state, and the boot clocks are in
    range. -/
theorem rv_family_boot_boundary {trace : Data babyBearModulus} {initial : RV.State} {cells : List Cell}
    {program : List RVProgramEntry}
    {inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.importedLayout)}
    (inputs : RVNativeBootBoundary trace initial cells program inits) :
    RVExecutionBoundary trace initial cells program :=
  ⟨⟨inputs.distinct, inputs.aligned, inputs.image,
    ⟨(4, 0), by rw [inputs.initialPC, initialStateRV, inputs.pc]⟩, inputs.programImage,
    ROMView.native_clocks (by decide)
      (boot_seed_image InitsTeardowns.standalone_claim.1 inputs.topBits inputs.seeds inputs.domain)
      inputs.initialPC⟩, inputs.rom⟩

end Airbender.Trace.Proofs
