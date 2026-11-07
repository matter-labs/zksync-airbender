import Airbender.Proofs.ReducedMachine.NativeWordMemoryPorts
import Airbender.Proofs.Trace.Values
import Airbender.Review.Helpers.Context.ReducedMachine

namespace Airbender.ReducedMachine.NativeWordMemoryPreservationProofs
open Native Trace Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- The exact actual ROM query bounds both returned limbs, including RAM-load
    shadow lookups. This is the checked fixed fixture, not an arbitrary ROM. -/
theorem rom_bounds {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (mask : w 12 = (wordMemoryMask false : ZMod mersenne31Modulus)) :
    (w 66).val < 65536 ∧ (w 67).val < 65536 := by
  have actual := (NativeWordMemoryShapeProofs.load_address holds mask).2.2.2
  have low := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[0]) actual
  have high := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[1]) actual
  simp only [Vector.getElem_map] at low high
  have bounds := NativeWordMemoryTableValues.rom_value_bounds (((w 61).val+65536*((w 62).val%64))/4)
  have small : 65536 < mersenne31Modulus := by decide
  constructor
  · change w 66 = _ at low
    rw [low,ZMod.val_natCast_of_lt (lt_trans bounds.1 small)]
    exact bounds.1
  · change w 67 = _ at high
    rw [high,ZMod.val_natCast_of_lt (lt_trans bounds.2 small)]
    exact bounds.2

/-- The load candidate selects certified ROM limbs or the earlier actual memory
    read; source/read ranges are internal induction obligations, not public inputs. -/
theorem load_candidate_bounds {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (mask : w 12 = (wordMemoryMask false : ZMod mersenne31Modulus))
    (read : (w 37).val < 65536 ∧ (w 38).val < 65536) :
    (w 116).val < 65536 ∧ (w 117).val < 65536 := by
  have actual := (NativeWordMemoryAccessProofs.load_access holds mask).candidate
  have low := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[0]) actual
  have high := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[1]) actual
  have selection := (NativeWordMemoryShapeProofs.load_address holds mask).2.2.1
  by_cases rom : (w 62).val < 64
  · have flag : w 64 = 0 := by simpa [rom] using selection
    have lo : w 116 = w 66 := by simpa [flag] using low
    have hi : w 117 = w 67 := by simpa [flag] using high
    simpa only [lo,hi] using rom_bounds holds mask
  · have flag : w 64 = 1 := by simpa [rom] using selection
    have lo : w 116 = w 37 := by simpa [flag] using low
    have hi : w 117 = w 38 := by simpa [flag] using high
    simpa only [lo,hi] using read

/-- Actual destination bounds use original rd/x0 only for LW. SW copies its
    earlier source directly to memory, retaining the store OLDREAD event. -/
theorem written_bounds {w : Nat → ZMod mersenne31Modulus} {entry : WordMemoryProgramEntry}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints NativeFixed.table))
    (fields : wordMemoryDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query)
    (read : (w 37).val < 65536 ∧ (w 38).val < 65536) :
    (w 43).val < 65536 ∧ (w 44).val < 65536 := by
  have decoded := NativeWordMemoryDecoderProofs.decoded_fields fields query
  cases mode : entry.data.family
  · have mask : w 12 = (wordMemoryMask false : ZMod mersenne31Modulus) := by simpa [mode] using decoded.mask
    have bounds := load_candidate_bounds holds mask read
    have actual := (NativeWordMemoryAccessProofs.load_access holds mask).written
    have low := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[0]) actual
    have high := congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[1]) actual
    have zero : w 8 = (if entry.data.rd = 0 then 1 else 0) := decoded.zero
    by_cases discard : entry.data.rd = 0
    · have flag : w 8 = 1 := by rw [if_pos discard] at zero; exact zero
      simp [flag] at low high
      simp [low,high]
    · have flag : w 8 = 0 := by rw [if_neg discard] at zero; exact zero
      have lo : w 43 = w 116 := by simpa [flag] using low
      have hi : w 44 = w 117 := by simpa [flag] using high
      simpa only [lo,hi] using bounds
  · have mask : w 12 = (wordMemoryMask true : ZMod mersenne31Modulus) := by simpa [mode] using decoded.mask
    have actual := (NativeWordMemoryAccessProofs.store_access holds mask).written
    have low : w 43 = w 37 := by simpa using congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[0]) actual
    have high : w 44 = w 38 := by simpa using congrArg (fun v : Vector (ZMod mersenne31Modulus) 2 => v[1]) actual
    simpa only [low,high] using read

/-- Exact readonly refreshes plus an earlier second-port read discharge the
    shared native time-induction rule. No preservation rule is supplied. -/
theorem row_write_rule (row : Row mersenne31Modulus NativeReducedFamily) {entry : WordMemoryProgramEntry}
    (native : FlatOperation.ConstraintsHoldFlat (environment row.assignment) (importedConstraints NativeFixed.table))
    (fields : wordMemoryDecoderFields entry.instruction = some entry.data)
    (query : row.decoderQuery = entry.query) : Trace.Proofs.RowWriteBoundsFromReads row := by
  cases row with
  | mk family w =>
    cases family
    intro port member reads
    change port ∈ importedConstraintsMemoryPorts at member
    simp [importedConstraintsMemoryPorts] at member
    rcases member with rfl | rfl | rfl
    · exact reads _ (by change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts]) (le_refl _)
    · exact reads _ (by change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts]) (le_refl _)
    · have second := reads importedConstraintsMemoryPorts[1]
        (by change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts]) (by
          change (decodeTimestamp w importedConstraintsTraceColumns.initialTime).value+1 ≤
            (decodeTimestamp w importedConstraintsTraceColumns.initialTime).value+2
          omega)
      rw [Trace.Proofs.read_word] at second
      change (w 37).val < 65536 ∧ (w 38).val < 65536 at second
      rw [Trace.Proofs.write_word]
      change (w 43).val < 65536 ∧ (w 44).val < 65536
      exact written_bounds native fields query second

end Airbender.ReducedMachine.NativeWordMemoryPreservationProofs
