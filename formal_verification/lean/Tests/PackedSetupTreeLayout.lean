import Airbender.Import.PackedSetupEmbed

namespace Tests.PackedSetupTreeLayout
open Airbender.Compiler.PackedSetupEquality
set_option warningAsError true

private def firstCodes : List BlockCode := [
  .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1,
  .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1,
  .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1,
  .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1,
  .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1,
  .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1,
  .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1,
  .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1,
  .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1,
  .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1,
  .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1,
  .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1,
  .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1,
  .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1,
  .affine 3 0 1, .affine 3 0 1]

private def middleCodes : List BlockCode := [
  .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1,
  .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1,
  .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1,
  .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1,
  .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1,
  .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1,
  .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1,
  .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1,
  .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1,
  .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1,
  .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1,
  .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1,
  .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1,
  .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1,
  .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1,
  .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1]

private def lastCodes : List BlockCode := [
  .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1,
  .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1, .affine 3 0 1]

private def source : List BlockCode := List.append firstCodes (List.append middleCodes lastCodes)

setup_code_tree tree from source => exact_layout

theorem valid_layout : tree.valid = true := by decide +kernel

end Tests.PackedSetupTreeLayout
