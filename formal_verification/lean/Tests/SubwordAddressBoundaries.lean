import Airbender.Proofs.SubwordMemory.Address
import Tests.SubwordAddressPart0
import Tests.SubwordAddressPart1

namespace Tests.SubwordAddressBoundaries
open Airbender Verification Arithmetic Trace SubwordMemory Tests.SubwordAddressWitness
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

theorem fields (sample : Fin 2) : SubwordMemory.decoderFields (entry sample).instruction = some (entry sample).data := by
  fin_cases sample <;> rfl

theorem original_wrap_decode : SailRV32.Functions.encdec_backwards 0x00108183 =
    .pure (.LOAD (1,.Regidx 1,.Regidx 3,false,1)) := by rfl

theorem original_negative_decode : SailRV32.Functions.encdec_backwards 0xffd08183 =
    .pure (.LOAD (4093,.Regidx 1,.Regidx 3,false,1)) := by rfl

theorem query (sample : Fin 2) : decoderQuery (assignment sample) = (entry sample).query := by
  fin_cases sample <;> decide +kernel

theorem native_addresses : ∀ sample : Fin 2, NativeAddress (assignment sample)
  | 0 => SubwordMemory.Proofs.native_address Tests.SubwordAddressPart0.constraints_0
    (by constructor <;> decide +kernel) (by constructor <;> decide +kernel) (by decide +kernel) (by decide +kernel)
  | 1 => SubwordMemory.Proofs.native_address Tests.SubwordAddressPart1.constraints_1
    (by constructor <;> decide +kernel) (by constructor <;> decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Both original signs and native low/high carries are retained. These are
    accepted native address regressions, not an original execution theorem. -/
theorem observed_wrap :
    (sourceWord (assignment ⟨0,by decide⟩)).toBitVec = 0xffffffff ∧
    (immediateWord (assignment ⟨0,by decide⟩)).toBitVec = 1 ∧
    (addressWord (assignment ⟨0,by decide⟩)).toBitVec = 0 ∧
    (cellWord (assignment ⟨0,by decide⟩)).toBitVec = 0 ∧ assignment ⟨0,by decide⟩ 21 = 1 := by
  decide +kernel

theorem observed_negative :
    (sourceWord (assignment ⟨1,by decide⟩)).toBitVec = 0 ∧
    (immediateWord (assignment ⟨1,by decide⟩)).toBitVec = 0xfffffffd ∧
    (addressWord (assignment ⟨1,by decide⟩)).toBitVec = 0xfffffffd ∧
    (cellWord (assignment ⟨1,by decide⟩)).toBitVec = 0xfffffffc ∧ assignment ⟨1,by decide⟩ 22 = 1 := by
  decide +kernel

end Tests.SubwordAddressBoundaries
