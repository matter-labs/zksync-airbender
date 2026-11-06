import Airbender.Review.Trace.Families.ReducedMachine.Decoder
import Airbender.Proofs.ShiftBinop.NativeSetup

namespace Tests.NativeReducedDecoder
open Airbender Trace ReducedMachine Native
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

-- Reuse only the original public words/state and their checked Sail byte-read/decode
-- lemmas. No old split-family decoder table or mask identity is transferred.
private def entries : Vector ShiftProgramEntry 12 :=
  #v[⟨0,0x2091b3,.RTYPE (.Regidx 2,.Regidx 1,.Regidx 3,.SLL),⟨.left,1,2,3,⟨0,0⟩,4099,1⟩⟩,
    ⟨4,0x20d1b3,.RTYPE (.Regidx 2,.Regidx 1,.Regidx 3,.SRL),⟨.right,1,2,3,⟨0,0⟩,69635,5⟩⟩,
    ⟨8,0x4020d1b3,.RTYPE (.Regidx 2,.Regidx 1,.Regidx 3,.SRA),⟨.arithmetic,1,2,3,⟨0,0⟩,102403,5⟩⟩,
    ⟨24,0x1f09193,.SHIFTIOP (31,.Regidx 1,.Regidx 3,.SLLI),⟨.left,1,0,3,⟨31,0⟩,4097,1⟩⟩,
    ⟨28,0x1f0d193,.SHIFTIOP (31,.Regidx 1,.Regidx 3,.SRLI),⟨.right,1,0,3,⟨31,0⟩,69633,5⟩⟩,
    ⟨32,0x41f0d193,.SHIFTIOP (31,.Regidx 1,.Regidx 3,.SRAI),⟨.arithmetic,1,0,3,⟨1055,0⟩,102401,5⟩⟩,
    ⟨48,0x209033,.RTYPE (.Regidx 2,.Regidx 1,.Regidx 0,.SLL),⟨.left,1,2,0,⟨0,0⟩,4099,1⟩⟩,
    ⟨52,0x20d033,.RTYPE (.Regidx 2,.Regidx 1,.Regidx 0,.SRL),⟨.right,1,2,0,⟨0,0⟩,69635,5⟩⟩,
    ⟨56,0x4020d033,.RTYPE (.Regidx 2,.Regidx 1,.Regidx 0,.SRA),⟨.arithmetic,1,2,0,⟨0,0⟩,102403,5⟩⟩,
    ⟨72,0x1f09013,.SHIFTIOP (31,.Regidx 1,.Regidx 0,.SLLI),⟨.left,1,0,0,⟨31,0⟩,4097,1⟩⟩,
    ⟨76,0x1f0d013,.SHIFTIOP (31,.Regidx 1,.Regidx 0,.SRLI),⟨.right,1,0,0,⟨31,0⟩,69633,5⟩⟩,
    ⟨80,0x41f0d013,.SHIFTIOP (31,.Regidx 1,.Regidx 0,.SRAI),⟨.arithmetic,1,0,0,⟨1055,0⟩,102401,5⟩⟩]

private def publicIndex (i : Fin 12) : Fin 25 :=
  #v[0,1,2,6,7,8,12,13,14,18,19,20][i]

theorem selected_fields (i : Fin 12) :
    shiftDecoderFields entries[i].instruction = some entries[i].data := by
  fin_cases i <;> rfl

theorem original_public_bytes (i : Fin 12) :
    Reference.Sail.run (SailRV32.Functions.encdec_backwards entries[i].bits)
      ShiftBinop.NativeSetup.before = .ok entries[i].instruction ShiftBinop.NativeSetup.before := by
  have bits : entries[i].bits = ShiftBinop.NativeSetup.words[(publicIndex i).val] := by
    fin_cases i <;> decide +kernel
  have instruction : entries[i].instruction = ShiftBinop.NativeSetup.instructions[(publicIndex i).val] := by
    fin_cases i <;> rfl
  rw [bits,instruction]
  exact ShiftBinop.Proofs.native_fixture_decode (publicIndex i)

/-- Every original public slot, including unsupported holes, runs the same Sail decoder. -/
theorem original_public_slots (i : Fin 25) :
    programSlotRunWith shiftDecoderFields ShiftBinop.NativeSetup.before (BitVec.ofNat 32 (4 * i.val)) =
      some ((shiftDecoderFields ShiftBinop.NativeSetup.instructions[i.val]).map fun data =>
        (⟨BitVec.ofNat 32 (4 * i.val),ShiftBinop.NativeSetup.words[i.val],
          ShiftBinop.NativeSetup.instructions[i.val],data⟩ : ShiftProgramEntry)) := by
  simp only [programSlotRunWith,ShiftBinop.Proofs.native_fixture_words,
    ShiftBinop.Proofs.native_fixture_decode,bind,Option.bind,pure]

theorem encoded_arithmetic_immediate :
    entries[5].data.immediate = (⟨1055,0⟩ : Arithmetic.Word) ∧
      entries[11].data.immediate = (⟨1055,0⟩ : Arithmetic.Word) := ⟨rfl,rfl⟩

theorem original_x0_masks :
    entries[6].data.mask = 4099 ∧ entries[7].data.mask = 69635 ∧ entries[8].data.mask = 102403 ∧
      entries[9].data.mask = 4097 ∧ entries[10].data.mask = 69633 ∧ entries[11].data.mask = 102401 := by
  decide +kernel

theorem out_of_profile_rejected :
    shiftDecoderFields (.REV8 (.Regidx 1,.Regidx 3)) = none ∧
      shiftDecoderFields (.SHIFTIOP (32,.Regidx 1,.Regidx 3,.SLLI)) = none ∧
      shiftDecoderFields (.SHIFTIOP (63,.Regidx 1,.Regidx 3,.SRLI)) = none ∧
      shiftDecoderFields (.SHIFTIOP (32,.Regidx 1,.Regidx 3,.SRAI)) = none ∧
      shiftDecoderFields (.RTYPE (.Regidx 2,.Regidx 1,.Regidx 3,.ADD)) = none := by
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

/-- Public membership includes padding; native equations, not a padding-exclusion premise, reject it. -/
theorem padding_cannot_be_selected {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints fixed)) :
    (SparseDecoderSetup.table (p := mersenne31Modulus) (⟨[none],3⟩ : SparseDecoderSetup ShiftMode)).Contains #[]
      (Vector.replicate 10 (-1)) ∧ decoderQuery w ≠ Vector.replicate 10 (-1) := by
  exact ⟨⟨⟨0,by decide⟩,rfl⟩,NativeShiftDecoderProofs.padding_excluded holds⟩

theorem corrupted_zero_flag_rejected {w : Nat → ZMod mersenne31Modulus} (i : Fin 12)
    (query : decoderQuery w = entries[i].query)
    (wrong : rdZeroFlag w ≠ if entries[i].data.rd = 0 then 1 else 0) : False :=
  wrong (NativeShiftDecoderProofs.decoded_fields (selected_fields i) query).zero

end Tests.NativeReducedDecoder
