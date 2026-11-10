module
public import Human.Helpers.Delegation.RVDecoder
public import Slop.Trace.RVFetch
public import Slop.Trace.DecoderBits
public import Slop.Trace.Program
public import Slop.AddSub.Selectors
public import Slop.AddSub.PC
public import Slop.Delegation.CallerRequests
public import Slop.Deleg.Effect
public import Slop.Defs.Circuits.AddSub.Artifact
public import Slop.Defs.Helpers.Core.Word

@[expose] public section

/-! RV siblings of the caller decoder and PC proofs (`Decoder.lean`, `CallerPC.lean`): the public caller entry comes
    from `rvProgramImage` (`RV.decode` of the ROM image), so the row's instruction is `.delegate k` and `RV.step` at its
    PC is the delegation call. No Sail state, `Configured` or interpreter fact. -/

namespace Airbender.Delegation.Caller.Proofs
open Trace Arithmetic
set_option warningAsError true

theorem rv_fields_delegate {i : RV.Instr} {data : DecoderData Family}
    (fields : rvDecoderFields i = some data) : i = .delegate data.family.rvKind := by
  cases i <;> simp only [rvDecoderFields, reduceCtorEq] at fields
  rename_i k
  cases k <;> simp only [Option.some.injEq, reduceCtorEq] at fields <;> subst fields <;> rfl

theorem rv_source_of_image {before : RV.State} {addresses : List (BitVec 32)}
    {program : List RVProgramEntry} (image : rvProgramImage before addresses = some program)
    (entry : RVProgramEntry) (present : entry ∈ program) : RVSource before entry := by
  obtain ⟨pc, _, built⟩ := mem_rvProgramImage image entry present
  have same := (rvProgramEntryWith_some built).1
  subst same
  exact built

/-- A public caller entry decodes to its family's delegation, and `RV.step` at its PC (public ROM image) is that call. -/
theorem rv_source_call {before : RV.State} {entry : RVProgramEntry} (source : RVSource before entry) :
    RV.decode entry.bits = some (.delegate entry.data.family.rvKind) ∧
    ∀ s : RV.State, s.rom = before.rom → s.pc = entry.pc →
      RV.step s = RV.exec s (.delegate entry.data.family.rvKind) := by
  obtain ⟨_, guard, bits, i, decoded, fields⟩ := rvProgramEntryWith_some source
  have instruction := rv_fields_delegate fields
  subst instruction
  refine ⟨decoded, ?_⟩
  intro s rom pc
  obtain ⟨_, step⟩ := rv_step_fetch s before rom entry.pc pc guard
  rw [step, ← bits, decoded]
  rfl

theorem rv_public_source [Fact p.Prime] {before : RV.State} {addresses : List (BitVec 32)}
    {program : List RVProgramEntry} {w : Nat → ZMod p}
    (image : rvProgramImage before addresses = some program)
    (member : (rvDecoderTable program).Contains #[] (nativeQuery w)) :
    ∃ entry ∈ program, RVSource before entry ∧ nativeQuery w = rvQuery entry := by
  change ∃ i : Fin program.length, nativeQuery w = rvQuery (program.get i) at member
  obtain ⟨i, equal⟩ := member
  exact ⟨program.get i, List.get_mem _ _, rv_source_of_image image _ (List.get_mem _ _), equal⟩

theorem rv_query_csr (hp : 65536 < p) {w : Nat → ZMod p} {entry : RVProgramEntry}
    (equal : nativeQuery w = rvQuery entry) :
    (Requests.caller w).csr = Requests.csr entry.data.family := by
  have field := congrArg (fun values : Vector (ZMod p) 9 => values[3]) equal
  change w 6 = (Requests.csr entry.data.family : ZMod p) at field
  have bound : Requests.csr entry.data.family < p := by
    cases entry.data.family <;> simp only [Requests.csr] <;> omega
  simp [Requests.caller, AddSub.importedConstraintsDecoderColumns,
    field, ZMod.val_natCast_of_lt bound]

theorem rv_query_selected [Fact p.Prime] (hp : 65536 < p) {w : Nat → ZMod p}
    {entry : RVProgramEntry}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w) AddSub.importedConstraints)
    (equal : nativeQuery w = rvQuery entry) : Requests.Selected w := by
  have flags := (AddSub.Proofs.local_flags constraints).2
  have boolean : ∀ i : Fin 9, w #[10, 11, 12, 13, 14, 15, 16, 17, 18][i] = 0 ∨
      w #[10, 11, 12, 13, 14, 15, 16, 17, 18][i] = 1 := by
    intro i
    have bit := flags i
    fin_cases i <;> simpa using bit
  have packed := congrArg (fun q : Vector (ZMod p) 9 => q[8]) equal
  change (∑ i : Fin 9, (2 ^ i.val : Nat) * w #[10, 11, 12, 13, 14, 15, 16, 17, 18][i]) =
    (128 : ZMod p) at packed
  have bits := Trace.Proofs.unpack_decoder_bits (by omega) (by decide) boolean packed
  exact bits 7

theorem rv_query_pc (hp : 65536 < p) {w : Nat → ZMod p} {entry : RVProgramEntry}
    (equal : nativeQuery w = rvQuery entry) : initialPC w = Word.ofBitVec entry.pc := by
  have low := congrArg (fun values : Vector (ZMod p) 9 => values[0]) equal
  have high := congrArg (fun values : Vector (ZMod p) 9 => values[1]) equal
  change w 0 = ((Word.ofBitVec entry.pc).lo : ZMod p) at low
  change w 1 = ((Word.ofBitVec entry.pc).hi : ZMod p) at high
  change (⟨(w 0).val, (w 1).val⟩ : Word) = Word.ofBitVec entry.pc
  exact Trace.Proofs.word_of_pc_query hp low high

theorem rv_caller_binding [Fact p.Prime] (hp : 65536 < p)
    {before : RV.State} {addresses : List (BitVec 32)}
    {program : List RVProgramEntry} {w : Nat → ZMod p}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w) AddSub.importedConstraints)
    (image : rvProgramImage before addresses = some program)
    (member : (rvDecoderTable program).Contains #[] (nativeQuery w)) :
    RVBinding w before program := by
  obtain ⟨entry, entryMember, source, equal⟩ := rv_public_source image member
  have selected := rv_query_selected hp constraints equal
  obtain ⟨read, write, low, high⟩ := Requests.Proofs.caller_tokens constraints selected
  have sourceIndex := congrArg (fun fields : Vector (ZMod p) 9 => fields[2]) equal
  have destinationIndex := congrArg (fun fields : Vector (ZMod p) 9 => fields[4]) equal
  change w 5 = 0 at sourceIndex
  change w 7 = 0 at destinationIndex
  have zero : destination w = ⟨0, 0⟩ := by
    simp [destination, writeToken, MemoryToken.word, MemoryPort.writeCode,
      WordColumns.code, WordColumns.evaluate, AddSub.importedConstraintsMemoryPorts,
      low, high]
  obtain ⟨decoded, step⟩ := rv_source_call source
  refine ⟨⟨entry, entryMember, source, decoded, step, rv_query_csr hp equal⟩, read, write, zero, ?_, ?_, ?_⟩
  · simp [sourceToken, readToken, AddSub.importedConstraintsMemoryPorts,
      MemoryAddress.code, Cell.addressCode, sourceIndex]
  · simp [destinationToken, writeToken, AddSub.importedConstraintsMemoryPorts,
      MemoryAddress.code, Cell.addressCode, destinationIndex]
  · intro state
    have readZero : (Cell.register 0).readRV state = some 0 := by
      simp [Cell.readRV, RV.State.getReg]
    refine ⟨readZero, ?_⟩
    have value : (destination w).toBitVec = 0 := by rw [zero]; rfl
    simp only [Cell.applyRV, value, readZero, ite_true]

theorem rv_pc_binding [Fact p.Prime] (hp : 196608 < p)
    (inverse : (-30720 : ZMod p) * 65536 = 1)
    {before : RV.State} {addresses : List (BitVec 32)}
    {program : List RVProgramEntry} {w : Nat → ZMod p}
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w) AddSub.importedConstraints)
    (image : rvProgramImage before addresses = some program)
    (member : (rvDecoderTable program).Contains #[] (nativeQuery w)) :
    RVPCBinding w before program := by
  obtain ⟨entry, present, source, equal⟩ := rv_public_source image member
  have initial := rv_query_pc (by omega) equal
  have mapping : AddSub.PCMapping (initialPC w) (finalPC w) w := by
    constructor
    · change w 0 = ((w 0).val : ZMod p)
      exact (ZMod.natCast_zmod_val _).symm
    · change w 1 = ((w 1).val : ZMod p)
      exact (ZMod.natCast_zmod_val _).symm
    · rfl
    · rfl
  have result := AddSub.Proofs.pc_successor hp inverse constraints mapping
    (initial.symm ▸ Word.ofBitVec_bound entry.pc)
  have advance := result.2.2
  refine ⟨⟨entry, present, source, initial⟩, AddSub.Proofs.pc_bounds constraints mapping, advance, ?_, ?_⟩
  · intro s pc
    change s.pc + 4 = _
    rw [pc, advance]
  · intro s t rom pc stepped
    have atEntry : s.pc = entry.pc := by
      rw [pc, initial, Word.ofBitVec_roundtrip]
    rw [(rv_source_call source).2 s rom atEntry] at stepped
    obtain ⟨effect, _, applied⟩ := Option.bind_eq_some_iff.mp stepped
    rw [(RV.applyEffect_some applied).2.1, pc, advance]

end Airbender.Delegation.Caller.Proofs
