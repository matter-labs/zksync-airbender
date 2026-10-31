import Airbender.Proofs.GKRProtocol.PublicProgramSetup

namespace Airbender.Trace.NativeDecoder.ProgramRows.Proofs
open Airbender.Trace.NativeDecoder.ProgramRows
set_option warningAsError true

/-- A noncaller native entry survives in the ordinary public program. -/
theorem native_inl_member (config : Config) (initial : Reference.RiscV.Sail.State)
    (text : List (BitVec 32)) (entry : PooledProgramEntry)
    (member : Sum.inl entry ∈ nativeProgramOf config initial text) :
    entry ∈ programOf config initial text := by
  obtain ⟨⟨bits, index⟩, inText, selected⟩ := List.mem_filterMap.mp member
  cases caller : callerEntry config initial bits index with
  | some c => simp [nativeEntry, caller] at selected
  | none =>
    cases word : wordEntry config initial bits index with
    | none => simp [nativeEntry, caller, word] at selected
    | some found =>
      simp [nativeEntry, caller, word] at selected
      cases selected
      exact List.mem_filterMap.mpr ⟨(bits, index), inText, word⟩

/-- A virtual caller entry survives in the separate public caller program. -/
theorem native_inr_member (config : Config) (initial : Reference.RiscV.Sail.State)
    (text : List (BitVec 32)) (caller : CallerEntry)
    (member : Sum.inr caller ∈ nativeProgramOf config initial text) :
    caller ∈ callerProgramOf config initial text := by
  obtain ⟨⟨bits, index⟩, inText, selected⟩ := List.mem_filterMap.mp member
  cases parsed : callerEntry config initial bits index with
  | none => simp [nativeEntry, parsed] at selected
  | some found =>
    simp [nativeEntry, parsed] at selected
    cases selected
    exact List.mem_filterMap.mpr ⟨(bits, index), inText, parsed⟩

end Airbender.Trace.NativeDecoder.ProgramRows.Proofs

namespace Airbender.Compiler
open Airbender.Trace Airbender.Trace.NativeDecoder Reference.RiscV.Sail
set_option warningAsError true

/-- A range-checked query in the public unrolled decoder setup is either an
ordinary instruction or a virtual caller, both sourced from the initial Sail
image. The caller branch always uses the ADD/SUB decoder family. -/
theorem unrolled_active_public_case
    {config : ProgramRows.Config} {initial : State} {text : List (BitVec 32)}
    {capacity : Nat} {masks : PooledFamily → ProgramRows.Mask}
    {columns : PooledFamily → List (List (ZMod babyBearModulus))}
    (setup : UnrolledProgramSetup config initial text capacity masks columns)
    (family : PooledFamily) (query : List (ZMod babyBearModulus))
    (member : query ∈ columns family)
    (bounded : (query.head?.getD 0).val < 65536) :
    (∃ entry ∈ ProgramRows.programOf config initial text,
      entry.SourceWith initial config.fields ∧ entry.data.family = family ∧
        query = ProgramRows.maskRow (masks family) entry.query) ∨
    (∃ caller ∈ ProgramRows.callerProgramOf config initial text,
      caller.Source initial config.delegationCSR ∧ family = .addSub ∧
        query = ProgramRows.maskRow (masks family) caller.query) := by
  obtain ⟨item, inProgram, source, selected, equal⟩ :=
    unrolled_active_public_source setup family query member bounded
  cases item with
  | inl entry =>
    left
    exact ⟨entry, ProgramRows.Proofs.native_inl_member config initial text entry inProgram,
      source, selected, equal⟩
  | inr caller =>
    right
    exact ⟨caller, ProgramRows.Proofs.native_inr_member config initial text caller inProgram,
      source, selected.symm, equal⟩

end Airbender.Compiler

namespace Airbender.Trace.NativeDecoder.UnifiedProgramRows.Proofs
open Airbender.Trace.NativeDecoder.UnifiedProgramRows
open Airbender.Trace.NativeDecoder.ProgramRows
set_option warningAsError true

/-- The unified ordinary projection retains its public source entry. -/
theorem native_inl_member (initial : Reference.RiscV.Sail.State)
    (text : List (BitVec 32)) (ordinary : UnifiedReduced.ProgramEntry)
    (member : Sum.inl ordinary ∈ programOf initial text) :
    ordinary ∈ ordinaryProgramOf initial text := by
  exact List.mem_filterMap.mpr ⟨Sum.inl ordinary, member, rfl⟩

/-- The unified caller projection retains its native virtual caller. -/
theorem native_inr_member (initial : Reference.RiscV.Sail.State)
    (text : List (BitVec 32)) (caller : CallerEntry)
    (member : Sum.inr caller ∈ programOf initial text) :
    caller ∈ callerProgramOf initial text := by
  obtain ⟨⟨bits, index⟩, inText, selected⟩ := List.mem_filterMap.mp member
  cases parsed : callerEntryWith delegationCSR initial bits index with
  | none =>
    simp [entry, parsed] at selected
    cases decoded : ProgramRows.decodeWord initial bits with
    | none => simp [decoded] at selected
    | some instruction =>
      cases fields : decoderFields instruction with
      | none => simp [decoded, fields] at selected
      | some data => simp [decoded, fields] at selected
  | some found =>
    simp [entry, parsed] at selected
    cases selected
    exact List.mem_filterMap.mpr ⟨(bits, index), inText, parsed⟩

end Airbender.Trace.NativeDecoder.UnifiedProgramRows.Proofs

namespace Airbender.Compiler
open Airbender.Trace Airbender.Trace.NativeDecoder Reference.RiscV.Sail
set_option warningAsError true

/-- The unified public setup likewise classifies every active query into a
Sail-sourced ordinary instruction or virtual caller. -/
theorem unified_active_public_case
    {initial : State} {text : List (BitVec 32)} {capacity : Nat}
    {mask : ProgramRows.Mask}
    {columns : List (List (ZMod babyBearModulus))}
    (setup : UnifiedProgramSetup initial text capacity mask columns)
    (query : List (ZMod babyBearModulus)) (member : query ∈ columns)
    (bounded : (query.head?.getD 0).val < 65536) :
    (∃ ordinary ∈ UnifiedProgramRows.ordinaryProgramOf initial text,
      ordinary.SourceWith initial UnifiedProgramRows.decoderFields ∧
        query = ProgramRows.maskRow mask ordinary.query) ∨
    (∃ caller ∈ UnifiedProgramRows.callerProgramOf initial text,
      caller.Source initial UnifiedProgramRows.delegationCSR ∧
        query = ProgramRows.maskRow mask caller.query) := by
  obtain ⟨item, inProgram, source, equal⟩ :=
    unified_active_public_source setup query member bounded
  cases item with
  | inl ordinary =>
    left
    exact ⟨ordinary,
      UnifiedProgramRows.Proofs.native_inl_member initial text ordinary inProgram,
      source, equal⟩
  | inr caller =>
    right
    exact ⟨caller,
      UnifiedProgramRows.Proofs.native_inr_member initial text caller inProgram,
      source, equal⟩

end Airbender.Compiler
