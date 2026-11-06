import Airbender.Review.Circuits.ReducedMachine.Decoder
import Airbender.Proofs.ReducedMachine.NativeSelectors
import Airbender.Proofs.Trace.StatefulDecoderSetup

namespace Airbender.ReducedMachine.NativeShiftDecoderProofs
open Arithmetic Trace Native
open Airbender.Trace.Proofs
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- All selected Sail constructors retain bounded encoded immediates and exact native masks. -/
theorem field_bounds {instruction : SailRV32.instruction} {data : DecoderData ShiftMode}
    (fields : shiftDecoderFields instruction = some data) :
    data.immediate.Bounded ∧ ∃ useRegister : Bool,
      data.mask = data.family.mask useRegister ∧ data.funct3 = data.family.funct3 := by
  unfold shiftDecoderFields at fields
  split at fields
  all_goals try split at fields
  all_goals try simp only [Native.shiftFields] at fields
  all_goals first
    | (solve | cases fields)
    | (simp only [Option.some.injEq] at fields
       subst data
       constructor
       · first | exact Word.ofBitVec_bound _ | simp [Word.Bounded,limbBase]
       · first | exact ⟨false,rfl,rfl⟩ | exact ⟨true,rfl,rfl⟩)

/-- The actual eighteen Boolean bits bound the packed mask for every native row. -/
theorem packed_bound {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    (w 12).val < 262144 := by
  have b0 : (w 17).val ≤ 1 := NativeSelectorProofs.bit_bounds holds ⟨0,by decide⟩
  have b1 : (w 18).val ≤ 1 := NativeSelectorProofs.bit_bounds holds ⟨1,by decide⟩
  have b2 : (w 19).val ≤ 1 := NativeSelectorProofs.bit_bounds holds ⟨2,by decide⟩
  have b3 : (w 20).val ≤ 1 := NativeSelectorProofs.bit_bounds holds ⟨3,by decide⟩
  have b4 : (w 21).val ≤ 1 := NativeSelectorProofs.bit_bounds holds ⟨4,by decide⟩
  have b5 : (w 22).val ≤ 1 := NativeSelectorProofs.bit_bounds holds ⟨5,by decide⟩
  have b6 : (w 23).val ≤ 1 := NativeSelectorProofs.bit_bounds holds ⟨6,by decide⟩
  have b7 : (w 24).val ≤ 1 := NativeSelectorProofs.bit_bounds holds ⟨7,by decide⟩
  have b8 : (w 25).val ≤ 1 := NativeSelectorProofs.bit_bounds holds ⟨8,by decide⟩
  have b9 : (w 26).val ≤ 1 := NativeSelectorProofs.bit_bounds holds ⟨9,by decide⟩
  have b10 : (w 27).val ≤ 1 := NativeSelectorProofs.bit_bounds holds ⟨10,by decide⟩
  have b11 : (w 28).val ≤ 1 := NativeSelectorProofs.bit_bounds holds ⟨11,by decide⟩
  have b12 : (w 29).val ≤ 1 := NativeSelectorProofs.bit_bounds holds ⟨12,by decide⟩
  have b13 : (w 30).val ≤ 1 := NativeSelectorProofs.bit_bounds holds ⟨13,by decide⟩
  have b14 : (w 31).val ≤ 1 := NativeSelectorProofs.bit_bounds holds ⟨14,by decide⟩
  have b15 : (w 32).val ≤ 1 := NativeSelectorProofs.bit_bounds holds ⟨15,by decide⟩
  have b16 : (w 33).val ≤ 1 := NativeSelectorProofs.bit_bounds holds ⟨16,by decide⟩
  have b17 : (w 34).val ≤ 1 := NativeSelectorProofs.bit_bounds holds ⟨17,by decide⟩
  have packed := NativeSelectorProofs.packed holds
  omega

/-- Native mask equations reject both sparse holes and the all-minus-one tail. -/
theorem padding_excluded {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setup)) :
    decoderQuery w ≠ Vector.replicate 10 (-1) := by
  intro same
  have mask := congrArg (fun q : Vector (ZMod mersenne31Modulus) 10 => q[9]) same
  change w 12 = -1 at mask
  have small := packed_bound holds
  have last : (-1 : ZMod mersenne31Modulus).val = 2147483646 := by decide +kernel
  rw [mask,last] at small
  omega

/-- Public byte reads and original stateful Sail decoding produce the recovered entry. -/
theorem fetched_sources {w : Nat → ZMod mersenne31Modulus}
    {setup : SparseDecoderSetup ShiftMode} {before : Reference.RiscV.Sail.State}
    {count logCapacity : Nat} {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    (image : shiftDecoderSetupImage before count logCapacity = some setup)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints fixed))
    (member : setup.table.Contains #[] (decoderQuery w)) :
    ∃ entry ∈ setup.program, entry.SourceWith before shiftDecoderFields ∧ decoderQuery w = entry.query := by
  obtain ⟨entry,present,same⟩ := sparse_member member (padding_excluded holds)
  exact ⟨entry,present,(run_sparse_setup_sources image present).1,same⟩

/-- All actual source/destination/zero/immediate/mask fields follow from the original entry. -/
theorem decoded_fields {w : Nat → ZMod mersenne31Modulus} {entry : ShiftProgramEntry}
    (fields : shiftDecoderFields entry.instruction = some entry.data)
    (query : decoderQuery w = entry.query) : ShiftDecoded w entry := by
  obtain ⟨_,useRegister,mask,tag⟩ := field_bounds fields
  have q (slot : Fin 10) := congrArg (fun v : Vector (ZMod mersenne31Modulus) 10 => v[slot]) query
  refine ⟨⟨useRegister,?_⟩,q 2,q 3,q 4,q 5,?_,?_⟩
  · have same := q 9
    change w 12 = (entry.data.mask : ZMod mersenne31Modulus) at same
    simpa only [mask] using same
  · exact congrArg₂ (fun a b : ZMod mersenne31Modulus => #v[a,b]) (q 6) (q 7)
  · have same := q 8
    change w 11 = (entry.data.funct3 : ZMod mersenne31Modulus) at same
    simpa only [tag] using same

end Airbender.ReducedMachine.NativeShiftDecoderProofs
