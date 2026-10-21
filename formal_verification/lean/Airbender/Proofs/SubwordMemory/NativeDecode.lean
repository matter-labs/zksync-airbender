import Airbender.Review.Circuits.SubwordMemory.NativeData

namespace Airbender.SubwordMemory.Proofs
open Trace NativeSetup
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Pure reductions of the original decoder, separated from interpreting state. -/
theorem native_decoded_0 : SailRV32.Functions.encdec_backwards 0x00008183 =
    .pure (.LOAD (0,.Regidx 1,.Regidx 3,false,1)) := by rfl

theorem native_decoded_1 : SailRV32.Functions.encdec_backwards 0x00009183 =
    .pure (.LOAD (0,.Regidx 1,.Regidx 3,false,2)) := by rfl

theorem native_decoded_2 : SailRV32.Functions.encdec_backwards 0x0000c183 =
    .pure (.LOAD (0,.Regidx 1,.Regidx 3,true,1)) := by rfl

theorem native_decoded_3 : SailRV32.Functions.encdec_backwards 0x0000d183 =
    .pure (.LOAD (0,.Regidx 1,.Regidx 3,true,2)) := by rfl

theorem native_decoded_4 : SailRV32.Functions.encdec_backwards 0x00208023 =
    .pure (.STORE (0,.Regidx 2,.Regidx 1,1)) := by rfl

theorem native_decoded_5 : SailRV32.Functions.encdec_backwards 0x00209023 =
    .pure (.STORE (0,.Regidx 2,.Regidx 1,2)) := by rfl

theorem native_decoded_6 : SailRV32.Functions.encdec_backwards 0xfff08003 =
    .pure (.LOAD (4095,.Regidx 1,.Regidx 0,false,1)) := by rfl

theorem native_decoded_7 : SailRV32.Functions.encdec_backwards 0xfff09003 =
    .pure (.LOAD (4095,.Regidx 1,.Regidx 0,false,2)) := by rfl

theorem native_decoded_8 : SailRV32.Functions.encdec_backwards 0xfff0c003 =
    .pure (.LOAD (4095,.Regidx 1,.Regidx 0,true,1)) := by rfl

theorem native_decoded_9 : SailRV32.Functions.encdec_backwards 0xfff0d003 =
    .pure (.LOAD (4095,.Regidx 1,.Regidx 0,true,2)) := by rfl

theorem native_decoded_10 : SailRV32.Functions.encdec_backwards 0xfe208fa3 =
    .pure (.STORE (4095,.Regidx 2,.Regidx 1,1)) := by rfl

theorem native_decoded_11 : SailRV32.Functions.encdec_backwards 0xfe209fa3 =
    .pure (.STORE (4095,.Regidx 2,.Regidx 1,2)) := by rfl

theorem native_decoded_12 : SailRV32.Functions.encdec_backwards 0x0000a183 =
    .pure (.LOAD (0,.Regidx 1,.Regidx 3,false,4)) := by rfl

/-- Original decoding, including x0, sign extension inputs and the unsupported LW. -/
theorem native_fixture_decode (i : Fin 13) :
    Reference.Sail.run (SailRV32.Functions.encdec_backwards words[i.val]) before =
      .ok instructions[i.val] before := by
  have decoded : SailRV32.Functions.encdec_backwards words[i.val] = .pure instructions[i.val] := by
    fin_cases i
    · exact native_decoded_0
    · exact native_decoded_1
    · exact native_decoded_2
    · exact native_decoded_3
    · exact native_decoded_4
    · exact native_decoded_5
    · exact native_decoded_6
    · exact native_decoded_7
    · exact native_decoded_8
    · exact native_decoded_9
    · exact native_decoded_10
    · exact native_decoded_11
    · exact native_decoded_12
  rw [decoded]
  rfl

end Airbender.SubwordMemory.Proofs
