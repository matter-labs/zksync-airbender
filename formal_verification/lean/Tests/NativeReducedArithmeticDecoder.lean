import Airbender.Review.Trace.Families.ReducedMachine.ArithmeticDecoder
import Airbender.Proofs.AddSub.NativeSetup

namespace Tests.NativeReducedArithmeticDecoder
open Airbender Trace ReducedMachine Native
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

private def entries : Vector ArithmeticProgramEntry 6 :=
  #v[⟨0,0x001080b3,.RTYPE (.Regidx 1,.Regidx 1,.Regidx 1,.ADD),⟨.add,1,1,1,⟨0,0⟩,11,0⟩⟩,
    ⟨4,0xfff08113,.ITYPE (4095,.Regidx 1,.Regidx 2,.ADDI),⟨.addi,1,0,2,⟨65535,65535⟩,9,0⟩⟩,
    ⟨8,0x40208033,.RTYPE (.Regidx 2,.Regidx 1,.Regidx 0,.SUB),⟨.sub,1,2,0,⟨0,0⟩,8195,0⟩⟩,
    ⟨12,0x000071b7,.UTYPE (7,.Regidx 3,.LUI),⟨.lui,0,0,3,⟨28672,0⟩,513,7⟩⟩,
    ⟨16,0x00005217,.UTYPE (5,.Regidx 4,.AUIPC),⟨.auipc,0,0,4,⟨20480,0⟩,17,5⟩⟩,
    ⟨24,0x001080b3,.RTYPE (.Regidx 1,.Regidx 1,.Regidx 1,.ADD),⟨.add,1,1,1,⟨0,0⟩,11,0⟩⟩]

-- Only original public bytes/instruction decoding are reused. Old standalone
-- decoder masks, exported rows and native equation placement are not transferred.
private def oldEntries : Vector ProgramEntry 6 :=
  #v[AddSub.NativeSetup.addEntry,AddSub.NativeSetup.addiEntry,AddSub.NativeSetup.subEntry,
    AddSub.NativeSetup.luiEntry,AddSub.NativeSetup.auipcEntry,AddSub.NativeSetup.laterEntry]

theorem selected_fields (i : Fin 6) :
    arithmeticDecoderFields entries[i].instruction = some entries[i].data := by
  fin_cases i <;> rfl

theorem original_public_sources (i : Fin 6) :
    entries[i].SourceWith AddSub.NativeSetup.before arithmeticDecoderFields := by
  have member : oldEntries[i] ∈ AddSub.NativeSetup.setup.program := by
    fin_cases i <;> simp [oldEntries,AddSub.NativeSetup.setup,SparseDecoderSetup.program]
  have source := (Trace.Proofs.sparse_setup_sources AddSub.Proofs.native_fixture_image member).1
  have pc : entries[i].pc = oldEntries[i].pc := by fin_cases i <;> rfl
  have bits : entries[i].bits = oldEntries[i].bits := by fin_cases i <;> rfl
  have instruction : entries[i].instruction = oldEntries[i].instruction := by fin_cases i <;> rfl
  refine ⟨?_,?_,selected_fields i⟩
  · simpa only [pc,bits] using source.bytes
  · simpa only [bits,instruction] using source.decoded

theorem original_entry_construction (i : Fin 6) :
    programEntryRunWith arithmeticDecoderFields AddSub.NativeSetup.before entries[i].pc = some entries[i] := by
  have source := original_public_sources i
  simp only [programEntryRunWith,source.bytes,source.decoded,source.fields,bind,Option.bind,pure]

theorem sign_extension_and_raw_upper_bits :
    entries[1].data.immediate = (⟨65535,65535⟩ : Arithmetic.Word) ∧
    entries[3].data.funct3 = 7 ∧ entries[4].data.funct3 = 5 := ⟨rfl,rfl,rfl⟩

/-- Preserve every original arithmetic opcode even when its destination is x0. -/
theorem original_x0_forms :
    arithmeticDecoderFields (.RTYPE (.Regidx 2,.Regidx 1,.Regidx 0,.ADD)) =
      some ⟨.add,1,2,0,⟨0,0⟩,11,0⟩ ∧
    arithmeticDecoderFields (.RTYPE (.Regidx 2,.Regidx 1,.Regidx 0,.SUB)) =
      some ⟨.sub,1,2,0,⟨0,0⟩,8195,0⟩ ∧
    arithmeticDecoderFields (.ITYPE (4095,.Regidx 1,.Regidx 0,.ADDI)) =
      some ⟨.addi,1,0,0,⟨65535,65535⟩,9,0⟩ ∧
    arithmeticDecoderFields (.UTYPE (7,.Regidx 0,.LUI)) = some ⟨.lui,0,0,0,⟨28672,0⟩,513,7⟩ ∧
    arithmeticDecoderFields (.UTYPE (5,.Regidx 0,.AUIPC)) = some ⟨.auipc,0,0,0,⟨20480,0⟩,17,5⟩ := by
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem unsupported_shift_rejected :
    arithmeticDecoderFields (.RTYPE (.Regidx 2,.Regidx 1,.Regidx 3,.SLL)) = none := rfl

theorem padded_membership {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints fixed)) :
    (SparseDecoderSetup.table (p := mersenne31Modulus) (⟨[none],3⟩ : SparseDecoderSetup ArithmeticMode)).Contains #[]
      (Vector.replicate 10 (-1)) ∧ decoderQuery w ≠ Vector.replicate 10 (-1) :=
  ⟨⟨⟨0,by decide⟩,rfl⟩,NativeShiftDecoderProofs.padding_excluded holds⟩

theorem corrupted_zero_flag_rejected {w : Nat → ZMod mersenne31Modulus} (i : Fin 6)
    (query : decoderQuery w = entries[i].query)
    (wrong : rdZeroFlag w ≠ if entries[i].data.rd = 0 then 1 else 0) : False :=
  wrong (NativeArithmeticDecoderProofs.decoded_fields (selected_fields i) query).zero

/-- Raw U-type funct3 is derived from original bytes, not zeroed by family. -/
theorem corrupted_upper_funct3_rejected {w : Nat → ZMod mersenne31Modulus}
    (query : decoderQuery w = entries[3].query) : w 11 ≠ 0 := by
  have decoded := NativeArithmeticDecoderProofs.decoded_fields (selected_fields 3) query
  have funct3 := decoded.funct3
  change w 11 = 7 at funct3
  rw [funct3]
  decide +kernel

end Tests.NativeReducedArithmeticDecoder
