import Airbender.Proofs.GKRProtocol.ProgramSetupRows

namespace Airbender.Reference.Compiler.ProgramSetup
set_option warningAsError true
set_option Elab.async false
variable {F : Type} [Ring F] [DecidableEq F]

private theorem tagged_cases (layout : Layout) (fixed : Nat → List F)
    (decoder : List (List F)) (wordAt : Nat → BitVec 32) (index : Nat)
    (tagged : layout.tagged = true) :
    (inRegion layout.decoderStart layout.decoderWords index ∧
      genericRows layout fixed decoder wordAt index =
        packTagged layout.width 46
          (decoder[index - layout.decoderStart]?.getD (decoderPadding (layout.width - 1)))) ∨
    (∃ regionStart, layout.romStart = some regionStart ∧
      inRegion regionStart layout.romWords index ∧
      genericRows layout fixed decoder wordAt index =
        packTagged layout.width 34 (romPayload wordAt (index - regionStart))) ∨
    genericRows layout fixed decoder wordAt index = List.replicate layout.width 0 ∨
    ((fixed index).getLast?.getD 0 ≠ 46 ∧ (fixed index).getLast?.getD 0 ≠ 34 ∧
      genericRows layout fixed decoder wordAt index = fixed index) := by
  by_cases decoderTag : (fixed index).getLast?.getD 0 = 46
  · by_cases inside : inRegion layout.decoderStart layout.decoderWords index
    · exact Or.inl ⟨inside, tagged_decoder layout fixed decoder wordAt index tagged decoderTag inside⟩
    · exact Or.inr (Or.inr (Or.inl (by simp [genericRows, tagged, decoderTag, inside])))
  · by_cases romTag : (fixed index).getLast?.getD 0 = 34
    · have different : (34 : F) ≠ 46 := by simpa only [romTag] using decoderTag
      cases region : layout.romStart with
      | none =>
        exact Or.inr (Or.inr (Or.inl (by simp [genericRows, tagged, romTag, different, region])))
      | some regionStart =>
        by_cases inside : inRegion regionStart layout.romWords index
        · exact Or.inr (Or.inl ⟨regionStart, rfl, inside,
            by simp [genericRows, tagged, romTag, different, region, inside]⟩)
        · exact Or.inr (Or.inr (Or.inl
            (by simp [genericRows, tagged, romTag, different, region, inside])))
    · exact Or.inr (Or.inr (Or.inr ⟨decoderTag, romTag,
        tagged_fixed layout fixed decoder wordAt index tagged decoderTag romTag⟩))

omit [DecidableEq F] in
private theorem zero_tag (count : Nat) :
    ((List.replicate count (0 : F)).getLast?.getD 0) = 0 := by
  induction count with
  | zero => rfl
  | succ count previous =>
    simpa only [List.replicate_succ, List.getLast?_cons, Option.getD_some] using previous

/-- A decoder-tagged query must use the supplied decoder region. -/
theorem decoder_query_region (layout : Layout) (fixed : Nat → List F)
    (decoder : List (List F)) (wordAt : Nat → BitVec 32) (index : Nat)
    (tagged : layout.tagged = true)
    (nonzero : (46 : F) ≠ 0) (different : (46 : F) ≠ 34)
    (query : List F) (same : query = genericRows layout fixed decoder wordAt index)
    (tag : query.getLast?.getD 0 = 46) :
    inRegion layout.decoderStart layout.decoderWords index ∧
      query = packTagged layout.width 46
        (decoder[index - layout.decoderStart]?.getD (decoderPadding (layout.width - 1))) := by
  rcases tagged_cases layout fixed decoder wordAt index tagged with
    selected | ⟨regionStart, _, _, selected⟩ | selected | ⟨notDecoder, _, selected⟩
  · exact ⟨selected.1, same.trans selected.2⟩
  · have : (34 : F) = 46 := by simpa [same, selected, packTagged] using tag
    exact (different this.symm).elim
  · have : (0 : F) = 46 := by simpa only [same, selected, zero_tag] using tag
    exact (nonzero this.symm).elim
  · exact (notDecoder (by simpa only [same, selected] using tag)).elim

/-- A ROM-tagged query must use the supplied public word function. -/
theorem rom_query_region (layout : Layout) (fixed : Nat → List F)
    (decoder : List (List F)) (wordAt : Nat → BitVec 32) (index : Nat)
    (tagged : layout.tagged = true)
    (nonzero : (34 : F) ≠ 0) (different : (34 : F) ≠ 46)
    (query : List F) (same : query = genericRows layout fixed decoder wordAt index)
    (tag : query.getLast?.getD 0 = 34) :
    ∃ regionStart, layout.romStart = some regionStart ∧
      inRegion regionStart layout.romWords index ∧
      query = packTagged layout.width 34 (romPayload wordAt (index - regionStart)) := by
  rcases tagged_cases layout fixed decoder wordAt index tagged with
    ⟨_, selected⟩ | ⟨regionStart, region, inside, selected⟩ | selected | ⟨_, notROM, selected⟩
  · have : (46 : F) = 34 := by simpa [same, selected, packTagged] using tag
    exact (different this.symm).elim
  · exact ⟨regionStart, region, inside, same.trans selected⟩
  · have : (0 : F) = 34 := by simpa only [same, selected, zero_tag] using tag
    exact (nonzero this.symm).elim
  · exact (notROM (by simpa only [same, selected] using tag)).elim

/-- A nonzero helper tag retains the captured fixed row. -/
theorem fixed_query_region (layout : Layout) (fixed : Nat → List F)
    (decoder : List (List F)) (wordAt : Nat → BitVec 32) (index : Nat)
    (tagged : layout.tagged = true) (query : List F)
    (same : query = genericRows layout fixed decoder wordAt index)
    (nonzero : query.getLast?.getD 0 ≠ 0)
    (notDecoder : query.getLast?.getD 0 ≠ 46)
    (notROM : query.getLast?.getD 0 ≠ 34) : query = fixed index := by
  rcases tagged_cases layout fixed decoder wordAt index tagged with
    ⟨_, selected⟩ | ⟨_, _, _, selected⟩ | selected | ⟨_, _, selected⟩
  · exact (notDecoder (by simp [same, selected, packTagged])).elim
  · exact (notROM (by simp [same, selected, packTagged])).elim
  · exact (nonzero (by simpa only [same, selected] using zero_tag (F := F) layout.width)).elim
  · exact same.trans selected

/-- A query outside the decoder and ROM tags is fixed or zero padding. -/
theorem fixed_query_or_zero (layout : Layout) (fixed : Nat → List F)
    (decoder : List (List F)) (wordAt : Nat → BitVec 32) (index : Nat)
    (tagged : layout.tagged = true) (query : List F)
    (same : query = genericRows layout fixed decoder wordAt index)
    (notDecoder : query.getLast?.getD 0 ≠ 46)
    (notROM : query.getLast?.getD 0 ≠ 34) :
    query = fixed index ∨ query = List.replicate layout.width 0 := by
  rcases tagged_cases layout fixed decoder wordAt index tagged with
    ⟨_, selected⟩ | ⟨_, _, _, selected⟩ | selected | ⟨_, _, selected⟩
  · exact (notDecoder (by simp [same, selected, packTagged])).elim
  · exact (notROM (by simp [same, selected, packTagged])).elim
  · exact Or.inr (same.trans selected)
  · exact Or.inl (same.trans selected)

omit [DecidableEq F] in
/-- An active decoder payload cannot come from the missing-row sentinel. -/
theorem decoder_payload_member (decoder : List (List F)) (index count : Nat)
    (positive : 0 < count) (payload : List F)
    (same : decoder[index]?.getD (decoderPadding count) = payload)
    (active : payload.head? ≠ some (-1)) : payload ∈ decoder := by
  cases found : decoder[index]? with
  | none =>
    have sentinel : payload = decoderPadding count := by simpa [found] using same.symm
    exact (active (sentinel ▸ decoderPadding_head count positive)).elim
  | some item =>
    have equal : item = payload := by simpa [found] using same
    exact equal ▸ List.mem_of_getElem? found

/-- Match the full decoder payload. Its width comes from the public mask. -/
theorem tagged_decoder_query_member (layout : Layout) (fixed : Nat → List F)
    (decoder : List (List F)) (wordAt : Nat → BitVec 32) (index : Nat)
    (tagged : layout.tagged = true)
    (nonzero : (46 : F) ≠ 0) (different : (46 : F) ≠ 34)
    (positive : 0 < layout.width - 1)
    (widths : ∀ row ∈ decoder, row.length = layout.width - 1)
    (payload : List F) (payloadWidth : payload.length = layout.width - 1)
    (same : packTagged layout.width 46 payload = genericRows layout fixed decoder wordAt index)
    (active : payload.head? ≠ some (-1)) : payload ∈ decoder := by
  have selected := decoder_query_region layout fixed decoder wordAt index tagged nonzero different
    (packTagged layout.width 46 payload) same (by simp [packTagged])
  have rowWidth :
      (decoder[index - layout.decoderStart]?.getD (decoderPadding (layout.width - 1))).length =
        layout.width - 1 := by
    cases found : decoder[index - layout.decoderStart]? with
    | none => simp [decoderPadding]
    | some row => simpa only [found, Option.getD_some] using widths row (List.mem_of_getElem? found)
  have equal := packTagged_injective layout.width 46 payload _ (payloadWidth.trans rowWidth.symm) selected.2
  exact decoder_payload_member decoder (index - layout.decoderStart) (layout.width - 1)
    positive payload equal.symm active

/-- Untagged decoder rows also reject every sentinel outside the program. -/
theorem untagged_decoder_query_member (layout : Layout) (fixed : Nat → List F)
    (decoder : List (List F)) (wordAt : Nat → BitVec 32) (index : Nat)
    (untagged : layout.tagged = false) (positive : 0 < layout.width)
    (payload : List F) (same : payload = genericRows layout fixed decoder wordAt index)
    (active : payload.head? ≠ some (-1)) : payload ∈ decoder := by
  by_cases inside : inRegion layout.decoderStart layout.decoderWords index
  · have selected := untagged_decoder layout fixed decoder wordAt index untagged inside
    exact decoder_payload_member decoder (index - layout.decoderStart) layout.width positive payload
      (same.trans selected).symm active
  · have sentinel := same.trans (untagged_padding layout fixed decoder wordAt index untagged inside)
    exact (active (sentinel ▸ decoderPadding_head layout.width positive)).elim

/-- A complete ROM payload gives the public word at the selected address. -/
theorem rom_query_payload (layout : Layout) (fixed : Nat → List F)
    (decoder : List (List F)) (wordAt : Nat → BitVec 32) (index : Nat)
    (tagged : layout.tagged = true)
    (nonzero : (34 : F) ≠ 0) (different : (34 : F) ≠ 46)
    (payload : List F) (payloadWidth : payload.length = 3)
    (same : packTagged layout.width 34 payload = genericRows layout fixed decoder wordAt index) :
    ∃ wordIndex, wordIndex < layout.romWords ∧ payload = romPayload wordAt wordIndex := by
  obtain ⟨regionStart, _, inside, equal⟩ := rom_query_region layout fixed decoder wordAt index tagged
    nonzero different (packTagged layout.width 34 payload) same (by simp [packTagged])
  exact ⟨index - regionStart, inside.2,
    packTagged_injective layout.width 34 payload _ payloadWidth equal⟩

end Airbender.Reference.Compiler.ProgramSetup
