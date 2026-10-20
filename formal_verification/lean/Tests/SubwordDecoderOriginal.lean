import Tests.SubwordDecoderFixture

namespace Tests.SubwordDecoderOriginal
open Airbender Tests.SubwordDecoderFixture
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- First reduce the original decoder without interpreting or expanding a state. -/
theorem decoded_0 : SailRV32.Functions.encdec_backwards 0x00008183 =
    .pure (.LOAD (0,.Regidx 1,.Regidx 3,false,1)) := by rfl

theorem decoded_1 : SailRV32.Functions.encdec_backwards 0x0000d183 =
    .pure (.LOAD (0,.Regidx 1,.Regidx 3,true,2)) := by rfl

theorem decoded_2 : SailRV32.Functions.encdec_backwards 0x00008183 =
    .pure (.LOAD (0,.Regidx 1,.Regidx 3,false,1)) := by rfl

theorem decoded_3 : SailRV32.Functions.encdec_backwards 0x00009003 =
    .pure (.LOAD (0,.Regidx 1,.Regidx 0,false,2)) := by rfl

theorem decoded_4 : SailRV32.Functions.encdec_backwards 0x00208023 =
    .pure (.STORE (0,.Regidx 2,.Regidx 1,1)) := by rfl

theorem decoded_5 : SailRV32.Functions.encdec_backwards 0x00209023 =
    .pure (.STORE (0,.Regidx 2,.Regidx 1,2)) := by rfl

theorem decoded_6 : SailRV32.Functions.encdec_backwards 0x0000c183 =
    .pure (.LOAD (0,.Regidx 1,.Regidx 3,true,1)) := by rfl

end Tests.SubwordDecoderOriginal
