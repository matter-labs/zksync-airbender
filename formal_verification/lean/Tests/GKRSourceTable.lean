import GKRProtocol.TableNative.AddSubCached

namespace Tests.GKRSourceTable
open Airbender Airbender.Compiler
set_option warningAsError true
set_option maxRecDepth 32768

private def actual := TableNative.AddSubCached.native.nativeLayout
private def expected := TableNative.AddSubCached.native.sourcePlan.layout

theorem rejects_changed_table_offset :
    decide (({actual with offsets := 1 :: actual.offsets.drop 1} : LookupTableLayout) = expected) = false := by
  decide +kernel

theorem rejects_changed_decoder_boundary :
    decide (({actual with decoderOffset := actual.decoderOffset + 1} : LookupTableLayout) = expected) = false := by
  decide +kernel

theorem rejects_reversed_setup_columns :
    decide (TableNative.AddSubCached.native.genericSetupColumns.reverse =
      TableNative.AddSubCached.native.genericSetupColumns) = false := by decide +kernel

theorem rejects_timestamp_setup_for_range16 :
    decide (TableNative.AddSubCached.native.range16SetupColumns = [SourceSetupColumn.timestamp]) = false := by
  decide +kernel

theorem rejects_multiplicity_aliasing_original_variable :
    (List.range 42).all (fun index => !addressEqual
      (LookupSourceNative.AddSubCached.native.bank.address (LookupNative.AddSubCached.native.sourcePlacement index))
      (.BaseLayerWitness 0)) = false := by decide +kernel

end Tests.GKRSourceTable
