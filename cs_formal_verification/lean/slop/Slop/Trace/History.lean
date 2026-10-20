import Human.Helpers.Context.Model
import Slop.WordMemory.ArtifactChecks
import Slop.Trace.Rows
import Slop.Trace.ClockHistory

namespace Airbender.Trace.Proofs

variable {Kind : Type} [CircuitLayout Kind]

/-- Kernel-checked local obligations reused by the native matching proofs.
    Instances prove these from each family's imported constraints and metadata. -/
class ClockLaws (Kind : Type) [CircuitLayout Kind] (p : Nat) [Fact p.Prime] : Prop where
  finalBound : ∀ (rom : CircuitLayout.Setup (Kind := Kind) p) (row : Row p Kind),
    FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints rom) → (decodeTimestamp row.assignment row.columns.finalTime).Bounded
  advance : ∀ (_ : 2 * timestampBase + 4 < p)
    (_ : (-3840 : ZMod p) * 524288 = 1) (rom : CircuitLayout.Setup (Kind := Kind) p)
    (row : Row p Kind),
    FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints rom) → (decodeTimestamp row.assignment row.columns.initialTime).Bounded →
    (decodeTimestamp row.assignment row.columns.finalTime).value =
      (decodeTimestamp row.assignment row.columns.initialTime).value + 4
  portsClocks : ∀ row : Row p Kind, row.ports.map MemoryPort.clock = row.columns.ports
  offsets : ∀ row : Row p Kind, row.ports.toList.map (fun port => port.clock.offset) = [0, 1, 2]
  effects : ∀ (_ : 2 * timestampBase + 4 < p)
    (_ : (-3840 : ZMod p) * 524288 = 1) (rom : CircuitLayout.Setup (Kind := Kind) p)
    (row : Row p Kind),
    FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints rom) → ClockInputs row.columns row.assignment →
    ClockEffects row.columns row.assignment

instance [Fact p.Prime] : ClockLaws Family p where
  finalBound rom row h := by
    cases row with
    | mk family w =>
      cases family with
      | addSub => exact addSub_final_bound h
      | wordMemory => exact wordMemory_final_bound rom h
  advance hp inverse rom row h bound := by
    cases row with
    | mk family w =>
      cases family with
      | addSub => exact (addSub_step hp inverse h bound).2
      | wordMemory => exact (wordMemory_step hp inverse rom h bound).2
  portsClocks row := by
    cases row with
    | mk family w =>
      cases family with
      | addSub => exact AddSub.memory_clocks
      | wordMemory => exact WordMemory.memory_clocks
  offsets row := by
    cases row with
    | mk family w => cases family <;> rfl
  effects hp inverse rom row h inputs := by
    cases row with
    | mk family w =>
      cases family with
      | addSub => exact addSub_clock hp inverse h inputs
      | wordMemory => exact wordMemory_clock hp inverse rom h inputs

private theorem row_final_bound [Fact p.Prime] [ClockLaws Kind p]
    (rom : CircuitLayout.Setup (Kind := Kind) p) (row : Row p Kind)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints rom)) : (decodeTimestamp row.assignment row.columns.finalTime).Bounded :=
  ClockLaws.finalBound rom row h

private theorem row_advance [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    [ClockLaws Kind p] (inverse : (-3840 : ZMod p) * 524288 = 1)
    (rom : CircuitLayout.Setup (Kind := Kind) p) (row : Row p Kind)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment)
      (row.constraints rom)) (bound : (decodeTimestamp row.assignment row.columns.initialTime).Bounded) :
    (decodeTimestamp row.assignment row.columns.finalTime).value =
      (decodeTimestamp row.assignment row.columns.initialTime).value + 4 :=
  ClockLaws.advance hp inverse rom row h bound

theorem ports_clocks [Fact p.Prime] [ClockLaws Kind p] (row : Row p Kind) :
    row.ports.map MemoryPort.clock = row.columns.ports := ClockLaws.portsClocks row

theorem port_offset [Fact p.Prime] [ClockLaws Kind p] (row : Row p Kind)
    (port : MemoryPort) (member : port ∈ row.ports) : port.clock.offset < 4 := by
  have present : port.clock.offset ∈ row.ports.toList.map (fun port => port.clock.offset) :=
    List.mem_map.mpr ⟨port, by simpa using member, rfl⟩
  rw [ClockLaws.offsets row] at present
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with present | present | present <;> omega

/-- Native write-clock limbs stay bounded: alignment prevents an in-cycle offset
    from crossing the 19-bit low-limb boundary. -/
theorem write_time_of_room [Fact p.Prime] (hp : timestampBase < p) {base : ZMod p × ZMod p}
    (bound : (timeOfPair base).Bounded) {offset : Nat}
    (lowBound : base.1.val + offset < timestampBase) :
    (timeOfPair (base.1 + (offset : ZMod p), base.2)).Bounded ∧
      (timeOfPair (base.1 + (offset : ZMod p), base.2)).value = (timeOfPair base).value + offset := by
  have canonical : (base.1 + (offset : ZMod p)).val = base.1.val + offset := by
    calc
      (base.1 + (offset : ZMod p)).val = ((base.1.val + offset : Nat) : ZMod p).val := by
        simp only [Nat.cast_add, ZMod.natCast_zmod_val]
      _ = base.1.val + offset := by
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt (lt_trans lowBound hp)]
  constructor
  · exact ⟨by simpa [timeOfPair, canonical] using lowBound, bound.2⟩
  · simp only [timeOfPair, Timestamp.value, canonical]
    omega

theorem write_time [Fact p.Prime] (hp : timestampBase < p) {base : ZMod p × ZMod p}
    (bound : (timeOfPair base).Bounded) (aligned : (timeOfPair base).lo % 4 = 0)
    {offset : Nat} (ob : offset < 4) :
    (timeOfPair (base.1 + (offset : ZMod p), base.2)).Bounded ∧
      (timeOfPair (base.1 + (offset : ZMod p), base.2)).value = (timeOfPair base).value + offset := by
  apply write_time_of_room hp bound
  have lb := bound.1
  simp only [timeOfPair] at aligned lb
  norm_num [timestampBase] at lb ⊢
  omega

def clockSteps [Fact p.Prime] (trace : Data p Kind) : List (Timestamp × Timestamp) :=
  trace.rows.map fun row =>
    (decodeTimestamp row.assignment row.columns.initialTime,
      decodeTimestamp row.assignment row.columns.finalTime)

private theorem clock_matching [Fact p.Prime] {trace : Data p Kind} (accepted : Accepted trace) :
    (timeOfPair trace.initial.timestamp :: (clockSteps trace).map Prod.snd).Perm
      (timeOfPair trace.terminal.timestamp :: (clockSteps trace).map Prod.fst) := by
  simpa [clockSteps, List.map_map, Function.comp_def, Row.start, Row.finish,
    timeOfPair, rawPair, decodeTimestamp] using
    accepted.states.map (fun state => timeOfPair state.timestamp)

/-- Discharge the row-level clock interface from actual native tuple matching.
    Public initial clock conditions replace every per-row bound/alignment premise. -/
theorem clock_inputs [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    [ClockLaws Kind p] (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p Kind}
    (accepted : Accepted trace) (boundary : ClockBoundary trace) :
    ∀ row ∈ trace.rows, ClockInputs row.columns row.assignment := by
  have matching := clock_matching accepted
  have finalBounds : ∀ step ∈ clockSteps trace, step.2.Bounded := by
    intro step member
    obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp member
    exact row_final_bound trace.rom row (accepted.constraints row rowMember)
  have incoming := incoming_bounds matching boundary.initial finalBounds
  have initialBounds : ∀ row ∈ trace.rows,
      (decodeTimestamp row.assignment row.columns.initialTime).Bounded := by
    intro row member
    exact incoming _ (List.mem_map.mpr ⟨row, member, rfl⟩)
  have advances : ∀ step ∈ clockSteps trace, step.2.value = step.1.value + 4 := by
    intro step member
    obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp member
    exact row_advance hp inverse trace.rom row (accepted.constraints row rowMember) (initialBounds row rowMember)
  have alignments := incoming_alignment matching boundary.aligned advances
  have initialAligned : ∀ row ∈ trace.rows,
      (decodeTimestamp row.assignment row.columns.initialTime).lo % 4 = 0 := by
    intro row member
    exact low_alignment (alignments _ (List.mem_map.mpr ⟨row, member, rfl⟩))
  have writeBounds : ∀ row ∈ trace.rows, ∀ token ∈ row.writes, (timeOfPair token.time).Bounded := by
    intro row member token writeMember
    obtain ⟨port, portMember, rfl⟩ := List.mem_map.mp writeMember
    have offsetBound := port_offset row port (by simpa using portMember)
    exact (write_time (by omega) (base := rawPair row.assignment row.columns.initialTime)
      (initialBounds row member) (initialAligned row member) offsetBound).1
  intro row member
  refine ⟨initialBounds row member, initialAligned row member, ?_⟩
  intro clock clockMember
  rw [← ports_clocks row] at clockMember
  obtain ⟨port, portMember, rfl⟩ := Array.mem_map.mp clockMember
  let token : MemoryToken p :=
    ⟨port.address.code row.assignment, rawPair row.assignment port.clock.previous,
      port.readCode row.assignment⟩
  have readMember : token ∈ trace.rows.flatMap Row.reads := by
    refine List.mem_flatMap.mpr ⟨row, member, ?_⟩
    exact List.mem_map.mpr ⟨port, by simpa using portMember, rfl⟩
  have matched := accepted.memory.mem_iff.mpr (List.mem_append_right _ readMember)
  rcases List.mem_append.mp matched with initial | written
  · exact boundary.memory token initial
  · obtain ⟨writer, writerMember, tokenMember⟩ := List.mem_flatMap.mp written
    exact writeBounds writer writerMember token tokenMember

theorem trace_clocks [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    [ClockLaws Kind p] (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p Kind}
    (accepted : Accepted trace) (boundary : ClockBoundary trace) :
    ∀ row ∈ trace.rows, ClockEffects row.columns row.assignment := by
  intro row member
  have inputs := clock_inputs hp inverse accepted boundary row member
  have h := accepted.constraints row member
  exact ClockLaws.effects hp inverse trace.rom row h inputs

theorem trace_terminal_clock [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    [ClockLaws Kind p] (inverse : (-3840 : ZMod p) * 524288 = 1) {trace : Data p Kind}
    (accepted : Accepted trace) (boundary : ClockBoundary trace) :
    (timeOfPair trace.terminal.timestamp).value =
      (timeOfPair trace.initial.timestamp).value + 4 * trace.rows.length := by
  have effects := trace_clocks hp inverse accepted boundary
  have result := terminal_clock (clock_matching accepted) (by
    intro step member
    obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp member
    exact (effects row rowMember).advances)
  simpa only [clockSteps, List.length_map] using result

end Airbender.Trace.Proofs
