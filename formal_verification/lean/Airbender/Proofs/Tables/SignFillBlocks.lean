import Airbender.Review.Helpers.Tables.NativeShiftScalarData
import Airbender.Review.Helpers.Tables.ShiftScalars
import Mathlib.Tactic.IntervalCases

namespace Airbender.Verification.ShiftScalarProofs
open Setup NativeShiftScalars
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem sign_high_blocks : dataSignFill.columns[2].blocks.toList =
    [.affine 98304 0 0,
    .affine 32768 32768 0,
    .affine 32768 0 0,
    .affine 32768 49152 0,
    .affine 32768 0 0,
    .affine 32768 57344 0,
    .affine 32768 0 0,
    .affine 32768 61440 0,
    .affine 32768 0 0,
    .affine 32768 63488 0,
    .affine 32768 0 0,
    .affine 32768 64512 0,
    .affine 32768 0 0,
    .affine 32768 65024 0,
    .affine 32768 0 0,
    .affine 32768 65280 0,
    .affine 32768 0 0,
    .affine 32768 65408 0,
    .affine 32768 0 0,
    .affine 32768 65472 0,
    .affine 32768 0 0,
    .affine 32768 65504 0,
    .affine 32768 0 0,
    .affine 32768 65520 0,
    .affine 32768 0 0,
    .affine 32768 65528 0,
    .affine 32768 0 0,
    .affine 32768 65532 0,
    .affine 32768 0 0,
    .affine 32768 65534 0,
    .affine 32768 0 0,
    .affine 32768 65535 0,
    .affine 32768 0 0,
    .affine 32768 65535 0,
    .affine 32768 0 0,
    .affine 32768 65535 0,
    .affine 32768 0 0,
    .affine 32768 65535 0,
    .affine 32768 0 0,
    .affine 32768 65535 0,
    .affine 32768 0 0,
    .affine 32768 65535 0,
    .affine 32768 0 0,
    .affine 32768 65535 0,
    .affine 32768 0 0,
    .affine 32768 65535 0,
    .affine 32768 0 0,
    .affine 32768 65535 0,
    .affine 32768 0 0,
    .affine 32768 65535 0,
    .affine 32768 0 0,
    .affine 32768 65535 0,
    .affine 32768 0 0,
    .affine 32768 65535 0,
    .affine 32768 0 0,
    .affine 32768 65535 0,
    .affine 32768 0 0,
    .affine 32768 65535 0,
    .affine 32768 0 0,
    .affine 32768 65535 0,
    .affine 32768 0 0,
    .affine 32768 65535 0] := rfl

end Airbender.Verification.ShiftScalarProofs
