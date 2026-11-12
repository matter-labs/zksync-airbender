module
public import Proven.Compiler.DecoderTags
public import Proven.Compiler.Lookups.NativeRanges
public import Mathlib.Tactic.IntervalCases

@[expose] public section
namespace Airbender.Compiler.NativePublicSetup.Proofs
open Airbender Trace NativeArithmetic Metadata
set_option warningAsError true
set_option maxRecDepth 65536

private theorem vector_eta (query : Vector F 9) :
    query = #v[query[0], query[1], query[2], query[3], query[4], query[5], query[6], query[7], query[8]] := by
  apply Vector.ext
  intro index bound
  interval_cases index <;> rfl

/-- The packed native projection retains each selected logical coordinate. -/
theorem payload_fields (family : RVMachineDecoderFamily) (query : Vector F 9) :
    payload family query =
      (if hasFunct3 family then
        [query[0], query[1], query[2], query[3], query[4], query[5], query[6], query[7], query[8]]
      else [query[0], query[1], query[2], query[3], query[4], query[5], query[6], query[8]]) ++
      if tagged family then [46] else [] := by
  unfold payload maskRow
  rw [columns_binding, vector_eta query]
  cases family with
  | pooled family => cases family <;> kernel_rfl
  | unified => kernel_rfl

/-- All native decoder projections retain the complete incoming low PC limb. -/
theorem payload_first (family : RVMachineDecoderFamily) (query : Vector F 9) :
    ((payload family query)[0]?).getD 0 = query[0] := by
  rw [payload_fields]
  cases hasFunct3 family <;> cases tagged family <;> rfl

theorem payload_tag (family : RVMachineDecoderFamily) (isTagged : tagged family = true)
    (query : Vector F 9) : ((payload family query)[width family - 1]?).getD 0 = 46 := by
  rw [payload_fields]
  cases family with
  | pooled family =>
    cases family with
    | addSub => simp [tagged] at isTagged
    | jumpBranchSlt => kernel_rfl
    | mulDiv => kernel_rfl
    | shiftBinop => kernel_rfl
    | wordMemory => kernel_rfl
    | subwordMemory => kernel_rfl
  | unified => kernel_rfl

private theorem pc_not_sentinel (query : Vector F 9) (typed : query[0].val < 65536) :
    query[0] ≠ -1 := by
  intro equal
  have same := congrArg ZMod.val equal
  rw [show (-1 : F).val = 2013265920 from by kernel_rfl] at same
  omega

/-- Native matching cannot authenticate a decoder query with a fixed or padding row. -/
theorem decoder_region (initial : RV.State) (program : List RVMachineProgramEntry)
    (family : RVMachineDecoderFamily) (query : Vector F 9) (typed : query[0].val < 65536)
    (member : Contains initial program family 0 (payload family query)) :
    ∃ position, payload family query = decoderRow family program position := by
  obtain ⟨index, equal⟩ := member
  change payload family query = genericRow family initial program index.val at equal
  unfold genericRow at equal
  by_cases before : index.val < (NativeLookups.circuitFor family).offset_for_decoder_table
  · rw [ite_eq_left before] at equal
    by_cases isTagged : tagged family = true
    · have selected := payload_tag family isTagged query
      rw [equal] at selected
      exact False.elim (fixed_not_decoder family isTagged _ _ selected)
    · cases family with
      | pooled family =>
        cases family <;> simp_all [tagged, offset_binding, offset]
      | unified => simp [tagged] at isTagged
  · rw [ite_eq_right before] at equal
    by_cases inside : index.val - (NativeLookups.circuitFor family).offset_for_decoder_table < decoderCapacity
    · rw [ite_eq_left inside] at equal
      exact ⟨_, equal⟩
    · rw [ite_eq_right inside, width_binding] at equal
      by_cases isTagged : tagged family = true
      · have selected := payload_tag family isTagged query
        rw [equal, ite_eq_left isTagged] at selected
        have zero : ((List.replicate (width family) (0 : F))[width family - 1]?).getD 0 = 0 := by simp only [List.getElem?_replicate]; split <;> rfl
        rw [zero] at selected
        have impossible := congrArg ZMod.val selected
        change 0 = 46 at impossible
        omega
      · have first := payload_first family query
        rw [equal, ite_eq_right isTagged] at first
        have positive : 0 < width family := by
          cases family with
          | pooled family => cases family <;> decide +kernel
          | unified => decide +kernel
        have sentinel : ((List.replicate (width family) (-1 : F))[0]?).getD (0 : F) = (-1 : F) := by
          simp [positive]
        rw [sentinel] at first
        exact False.elim (pc_not_sentinel query typed first.symm)

/-- A complete payload determines all included coordinates. The sole omitted
    coordinate is the absent funct3 field and both public projections set it to zero. -/
theorem payload_injective (family : RVMachineDecoderFamily) (left right : Vector F 9)
    (middle : hasFunct3 family = false → left[7] = right[7])
    (equal : payload family left = payload family right) : left = right := by
  rw [payload_fields, payload_fields] at equal
  have fields := List.append_cancel_right equal
  by_cases full : hasFunct3 family = true
  · simp only [ite_eq_left full, List.cons.injEq] at fields
    apply Vector.ext
    intro index bound
    interval_cases index <;> simp_all
  · have absent : hasFunct3 family = false := by cases h : hasFunct3 family <;> simp_all
    have same := middle absent
    simp only [ite_eq_right full, List.cons.injEq] at fields
    apply Vector.ext
    intro index bound
    interval_cases index <;> simp_all

/-- A supported decoder slot is exactly its public native program projection. -/
theorem decoder_entry {initial : RV.State} {program : List RVMachineProgramEntry}
    {actual : ProgramLookupRows} (bound : Bound initial program actual)
    (family : RVMachineDecoderFamily) (query : Vector F 9) (typed : query[0].val < 65536)
    (omitted : hasFunct3 family = false → query[7] = 0)
    (position : Nat) (equal : payload family query = decoderRow family program position) :
    Trace.Machine.Decoded family query program := by
  cases slot : program[position]? with
  | none =>
    have first := payload_first family query
    rw [equal] at first
    unfold decoderRow at first
    rw [slot] at first
    cases family with
    | pooled family => cases family <;> simp [tagged, width_binding, width, hasFunct3] at first <;>
        exact False.elim (pc_not_sentinel query typed first.symm)
    | unified =>
      simp [tagged, width_binding, width, hasFunct3] at first
      exact False.elim (pc_not_sentinel query typed first.symm)
  | some entry =>
    by_cases matching : entry.data.family = family
    · have present : entry ∈ program := by
        obtain ⟨present, rfl⟩ := List.getElem?_eq_some_iff.mp slot
        exact List.getElem_mem present
      refine ⟨entry, present, matching, ?_⟩
      apply payload_injective family _ _ ?_ ?_
      · intro absent
        rw [omitted absent]
        have zero := bound.omitted entry present (⟨7, by decide⟩ : Fin 9)
        rw [matching, columns_binding] at zero
        have check : (columns family)[7]?.getD false = false := by
          cases family with
          | pooled family => cases family <;> simp_all [columns, hasFunct3]
          | unified => simp [hasFunct3] at absent
        have value := zero check
        change (entry.data.row entry.pc)[7] = 0 at value
        simp only [Vector.getElem_map]
        rw [value]
        rfl
      · cases selected : tagged family <;>
          simpa [decoderRow, slot, programRow, matching, payload, selected] using equal
    · have first := payload_first family query
      rw [equal] at first
      unfold decoderRow programRow at first
      rw [slot] at first
      simp only [Option.map_some, Option.getD_some, ite_eq_right matching, width_binding] at first
      cases family with
      | pooled family => cases family <;> simp [tagged, width, hasFunct3] at first <;>
          exact False.elim (pc_not_sentinel query typed first.symm)
      | unified =>
        simp [tagged, width, hasFunct3] at first
        exact False.elim (pc_not_sentinel query typed first.symm)

/-- Exact native matching authenticates the complete public program entry. -/
theorem decoded {initial : RV.State} {program : List RVMachineProgramEntry}
    {actual : ProgramLookupRows} (bound : Bound initial program actual)
    (family : RVMachineDecoderFamily) (query : Vector F 9) (typed : query[0].val < 65536)
    (omitted : hasFunct3 family = false → query[7] = 0)
    (member : Contains initial program family 0 (payload family query)) :
    Trace.Machine.Decoded family query program := by
  obtain ⟨position, equal⟩ := decoder_region initial program family query typed member
  exact decoder_entry bound family query typed omitted position equal

end Airbender.Compiler.NativePublicSetup.Proofs
