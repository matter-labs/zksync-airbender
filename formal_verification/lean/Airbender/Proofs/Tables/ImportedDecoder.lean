import Airbender.Review.Helpers.Decoder.ImportedProgram
import Airbender.Review.Helpers.Decoder.NativeData
import Airbender.Proofs.Trace.Program
import Airbender.Proofs.Tables.ConstantTail
import Airbender.Proofs.ExternalBoundary.Decoder

namespace Airbender.Trace.NativeDecoder.Proofs
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

/-- Public byte binding supplies the existing Sail source certificate for the
    program projected from imported text; decoder answers are conclusions. -/
theorem selected_sources {Kind : Type}
    {projection : SailRV32.instruction → Option (DecoderData Kind)}
    {before : Reference.RiscV.Sail.State} (bytes : SelectedBytes before) :
    ∀ entry ∈ selectedProgram projection, entry.SourceWith before projection := by
  intro entry member
  obtain ⟨index, _, selected⟩ := List.mem_filterMap.mp member
  have image : programEntryWith projection before (BitVec.ofNat 32 (4 * index.val)) =
      some entry := by
    unfold programEntryWith
    rw [bytes index]
    simp only [bind, Option.bind]
    unfold selectedEntry at selected
    cases decoded : SailRV32.Functions.encdec_backwards
        (BitVec.ofNat 32 ((ROM.nativeProgramData.text.get? index.val).getD 0)) with
    | pure instruction =>
      simpa only [decoded, bind, Option.bind] using selected
    | impure call continuation =>
      simp only [decoded, bind, Option.bind] at selected
      cases selected

  exact (Trace.Proofs.entry_source image).2

/-- A structural certificate over all stored blocks, with actual column
    extents, establishes a whole constant row without enumerating the tail. -/
theorem constant_row (data : TableData width) (expected : Vector Nat width)
    (checked : ∀ lane : Fin width,
      constantTail expected[lane] 0 data.columns[lane].blocks.toList = true)
    (extent : ∀ lane : Fin width,
      (data.columns[lane].blocks.toList.map Block.length).sum = data.length)
    (index : Nat) (bound : index < data.length) :
    data.columns.map (fun column => (column.get? index).getD 0) = expected := by
  apply Vector.ext
  intro lane hLane
  have actual := constantTail_sound _ _ _ (checked ⟨lane, hLane⟩) index (Nat.zero_le _)
    (by rw [extent]; exact bound)
  simpa only [Vector.getElem_map, Column.get?, Fin.getElem_fin, Option.getD_some] using
    congrArg (fun value => value.getD 0) actual

theorem normalize_first (setup : PackedSetup) (width : 0 < setup.width)
    (enabled : setup.columnsMask[0]?.getD false = true) (packed : Vector Nat setup.width) :
    (setup.normalize packed)[0] = packed[0] := by
  simp [PackedSetup.normalize, enabled,
    Array.extract_empty_of_stop_le_start (Nat.le_refl 0), width]

theorem signed_filler {p : Nat} :
    (signedValue (babyBearModulus - 1) : ZMod p) = -1 := by
  norm_num [signedValue, babyBearModulus]

def queryNat {Kind : Type} (entry : ProgramEntry Kind) : Vector Nat 10 :=
  let pc := Arithmetic.Word.ofBitVec entry.pc
  #v[pc.lo, pc.hi, entry.data.rs1.toNat, entry.data.rs2.toNat, entry.data.rd.toNat,
    entry.data.immediate.lo, entry.data.immediate.hi, entry.data.funct3, entry.data.mask, 46]

theorem queryNat_cast {Kind : Type} {p : Nat} (entry : ProgramEntry Kind) :
    (queryNat entry).map (fun n : Nat => (n : ZMod p)) = activeQuery entry.query := by
  apply Vector.ext
  intro column bound
  interval_cases column <;> simp [queryNat, ProgramEntry.query, activeQuery]

theorem signed_queryNat {Kind : Type} {p : Nat} (entry : ProgramEntry Kind)
    (small : ∀ lane : Fin 10, (queryNat entry)[lane] ≤ babyBearModulus / 2) :
    (queryNat entry).map (fun n => (signedValue n : ZMod p)) = activeQuery entry.query := by
  rw [← queryNat_cast entry]
  apply Vector.ext
  intro column bound
  have little : (queryNat entry)[column] ≤ babyBearModulus / 2 := small ⟨column, bound⟩
  simp only [Vector.getElem_map, signedValue]
  rw [if_pos little]
  simp only [Int.cast_natCast]

theorem activeQuery_injective {p : Nat} {left right : Vector (ZMod p) 9}
    (equal : activeQuery left = activeQuery right) : left = right := by
  apply Vector.ext
  intro column bound
  have value := congrArg (fun row : Vector (ZMod p) 10 => row[column]) equal
  simpa only [activeQuery, Vector.getElem_ofFn, dif_pos bound] using value

theorem padding_row (setup : PackedSetup) (expected : Vector Nat setup.width)
    (checked : ∀ lane : Fin setup.width,
      constantTail expected[lane] 0 setup.padding.columns[lane].blocks.toList = true)
    (extent : ∀ lane : Fin setup.width,
      (setup.padding.columns[lane].blocks.toList.map Block.length).sum = setup.padding.length)
    (zero : setup.padding.offset = 0)
    (index : Fin (setup.realRows.length + setup.padding.length))
    (outside : setup.realRows.length ≤ index.val) :
    setup.row index = setup.normalize expected := by
  have small : index.val - setup.realRows.length < setup.padding.length := by omega
  unfold PackedSetup.row
  simp only [if_neg (show ¬index.val < setup.realRows.length by omega)]
  rw [zero]
  simp only [Nat.zero_add]
  rw [constant_row setup.padding expected checked extent _ small]

/-- The typed query condition is the existing external PC-limb interface.
    The contents and padding obligations below are discharged from each actual
    imported setup, rather than supplied by the caller as table equivalence. -/
theorem decoder_member {Kind : Type} [DecidableEq Kind] {p : Nat} [Fact p.Prime]
    (hp : 65536 < p) (setup : PackedSetup)
    (program : List (ProgramEntry Kind)) (family : Kind)
    (real : ∀ index : Fin setup.realRows.length,
      (∃ entry ∈ program, entry.data.family = family ∧
        ((setup.row ⟨index.val, by have := index.isLt; omega⟩).map
          (fun n => (signedValue n : ZMod p))) = activeQuery entry.query) ∨
      (signedValue (setup.row ⟨index.val, by have := index.isLt; omega⟩)[0] : ZMod p) = -1)
    (padding : ∀ index : Fin (setup.realRows.length + setup.padding.length),
      setup.realRows.length ≤ index.val →
      (signedValue (setup.row index)[0] : ZMod p) = -1 ∨
      (signedValue (setup.row index)[9] : ZMod p) = 0)
    (query : Vector (ZMod p) 9) (typed : query[0].val < 65536)
    (holds : setup.table.Contains #[] (activeQuery query)) :
    (decoderTable program family).Contains #[] query := by
  change ∃ index : Fin (setup.realRows.length + setup.padding.length),
    activeQuery query = (setup.row index).map (fun n => (signedValue n : ZMod p)) at holds
  obtain ⟨index, equal⟩ := holds
  have low := congrArg (fun row : Vector (ZMod p) 10 => row[0]) equal
  have tag := congrArg (fun row : Vector (ZMod p) 10 => row[9]) equal
  have first (q : Vector (ZMod p) 9) : (activeQuery q)[0] = q[0] := by
    simp [activeQuery]
  have last (q : Vector (ZMod p) 9) : (activeQuery q)[9] = (46 : ZMod p) := by
    simp [activeQuery]
  simp only [first, Vector.getElem_map] at low
  simp only [last, Vector.getElem_map] at tag
  have notSentinel : query[0] ≠ (-1 : ZMod p) := by
    have actual := ExternalBoundary.Decoder.Proofs.typed_limb_ne_filler hp ⟨query[0].val, typed⟩
    simpa only [ZMod.natCast_zmod_val] using actual
  by_cases inside : index.val < setup.realRows.length
  · rcases real ⟨index.val, inside⟩ with ⟨entry, member, familyEq, shape⟩ | sentinel
    · have filtered : entry ∈ program.filter (fun e => e.data.family == family) := by
        simp [member, familyEq]
      obtain ⟨position, entryEq⟩ := List.mem_iff_get.mp filtered
      change ∃ i : Fin (program.filter fun e => e.data.family == family).length, _
      exact ⟨position, (activeQuery_injective (equal.trans shape)).trans
        (congrArg ProgramEntry.query entryEq).symm⟩
    · exact False.elim (notSentinel (low.trans sentinel))
  · rcases padding index (by omega) with sentinel | zeroTag
    · exact False.elim (notSentinel (low.trans sentinel))
    · have bad : (46 : ZMod p) = 0 := tag.trans zeroTag
      have divides : p ∣ 46 := (ZMod.natCast_eq_zero_iff 46 p).mp bad
      have bounded := Nat.le_of_dvd (by decide : 0 < 46) divides
      omega

end Airbender.Trace.NativeDecoder.Proofs
