import Airbender.Proofs.GKRProtocol.SourceFreshnessChecks.BlakeRoundCached.Data
import Airbender.Proofs.GKRProtocol.NumericQueryFrameBindings
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.SourceFreshnessChecks.BlakeRoundCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_data_binding view0 : (data.drop 0).take 8 = data0

numeric_data_binding piece0 : data0 = ((originalEntries.drop 0).take 8).map NumericFunctionalBaseChecks.encode

theorem binding0 : (data.drop 0).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 8 :=
  view0.trans (piece0.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 0 8))

numeric_data_binding view8 : (data.drop 8).take 8 = data8

numeric_data_binding piece8 : data8 = ((originalEntries.drop 8).take 8).map NumericFunctionalBaseChecks.encode

theorem binding8 : (data.drop 8).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 8).take 8 :=
  view8.trans (piece8.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 8 8))

numeric_data_binding view16 : (data.drop 16).take 8 = data16

numeric_data_binding piece16 : data16 = ((originalEntries.drop 16).take 8).map NumericFunctionalBaseChecks.encode

theorem binding16 : (data.drop 16).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 16).take 8 :=
  view16.trans (piece16.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 16 8))

numeric_data_binding view24 : (data.drop 24).take 8 = data24

numeric_data_binding piece24 : data24 = ((originalEntries.drop 24).take 8).map NumericFunctionalBaseChecks.encode

theorem binding24 : (data.drop 24).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 24).take 8 :=
  view24.trans (piece24.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 24 8))

numeric_data_binding view32 : (data.drop 32).take 8 = data32

numeric_data_binding piece32 : data32 = ((originalEntries.drop 32).take 8).map NumericFunctionalBaseChecks.encode

theorem binding32 : (data.drop 32).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 32).take 8 :=
  view32.trans (piece32.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 32 8))

numeric_data_binding view40 : (data.drop 40).take 8 = data40

numeric_data_binding piece40 : data40 = ((originalEntries.drop 40).take 8).map NumericFunctionalBaseChecks.encode

theorem binding40 : (data.drop 40).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 40).take 8 :=
  view40.trans (piece40.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 40 8))

numeric_data_binding view48 : (data.drop 48).take 8 = data48

numeric_data_binding piece48 : data48 = ((originalEntries.drop 48).take 8).map NumericFunctionalBaseChecks.encode

theorem binding48 : (data.drop 48).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 48).take 8 :=
  view48.trans (piece48.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 48 8))

numeric_data_binding view56 : (data.drop 56).take 8 = data56

numeric_data_binding piece56 : data56 = ((originalEntries.drop 56).take 8).map NumericFunctionalBaseChecks.encode

theorem binding56 : (data.drop 56).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 56).take 8 :=
  view56.trans (piece56.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 56 8))

numeric_data_binding view64 : (data.drop 64).take 8 = data64

numeric_data_binding piece64 : data64 = ((originalEntries.drop 64).take 8).map NumericFunctionalBaseChecks.encode

theorem binding64 : (data.drop 64).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 64).take 8 :=
  view64.trans (piece64.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 64 8))

numeric_data_binding view72 : (data.drop 72).take 8 = data72

numeric_data_binding piece72 : data72 = ((originalEntries.drop 72).take 8).map NumericFunctionalBaseChecks.encode

theorem binding72 : (data.drop 72).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 72).take 8 :=
  view72.trans (piece72.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 72 8))

numeric_data_binding view80 : (data.drop 80).take 8 = data80

numeric_data_binding piece80 : data80 = ((originalEntries.drop 80).take 8).map NumericFunctionalBaseChecks.encode

theorem binding80 : (data.drop 80).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 80).take 8 :=
  view80.trans (piece80.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 80 8))

numeric_data_binding view88 : (data.drop 88).take 8 = data88

numeric_data_binding piece88 : data88 = ((originalEntries.drop 88).take 8).map NumericFunctionalBaseChecks.encode

theorem binding88 : (data.drop 88).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 88).take 8 :=
  view88.trans (piece88.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 88 8))

numeric_data_binding view96 : (data.drop 96).take 8 = data96

numeric_data_binding piece96 : data96 = ((originalEntries.drop 96).take 8).map NumericFunctionalBaseChecks.encode

theorem binding96 : (data.drop 96).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 96).take 8 :=
  view96.trans (piece96.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 96 8))

numeric_data_binding view104 : (data.drop 104).take 8 = data104

numeric_data_binding piece104 : data104 = ((originalEntries.drop 104).take 8).map NumericFunctionalBaseChecks.encode

theorem binding104 : (data.drop 104).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 104).take 8 :=
  view104.trans (piece104.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 104 8))

numeric_data_binding view112 : (data.drop 112).take 8 = data112

numeric_data_binding piece112 : data112 = ((originalEntries.drop 112).take 8).map NumericFunctionalBaseChecks.encode

theorem binding112 : (data.drop 112).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 112).take 8 :=
  view112.trans (piece112.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 112 8))

numeric_data_binding view120 : (data.drop 120).take 8 = data120

numeric_data_binding piece120 : data120 = ((originalEntries.drop 120).take 8).map NumericFunctionalBaseChecks.encode

theorem binding120 : (data.drop 120).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 120).take 8 :=
  view120.trans (piece120.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 120 8))

numeric_data_binding view128 : (data.drop 128).take 8 = data128

numeric_data_binding piece128 : data128 = ((originalEntries.drop 128).take 8).map NumericFunctionalBaseChecks.encode

theorem binding128 : (data.drop 128).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 128).take 8 :=
  view128.trans (piece128.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 128 8))

numeric_data_binding view136 : (data.drop 136).take 8 = data136

numeric_data_binding piece136 : data136 = ((originalEntries.drop 136).take 8).map NumericFunctionalBaseChecks.encode

theorem binding136 : (data.drop 136).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 136).take 8 :=
  view136.trans (piece136.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 136 8))

numeric_data_binding view144 : (data.drop 144).take 8 = data144

numeric_data_binding piece144 : data144 = ((originalEntries.drop 144).take 8).map NumericFunctionalBaseChecks.encode

theorem binding144 : (data.drop 144).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 144).take 8 :=
  view144.trans (piece144.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 144 8))

numeric_data_binding view152 : (data.drop 152).take 8 = data152

numeric_data_binding piece152 : data152 = ((originalEntries.drop 152).take 8).map NumericFunctionalBaseChecks.encode

theorem binding152 : (data.drop 152).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 152).take 8 :=
  view152.trans (piece152.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 152 8))

numeric_data_binding view160 : (data.drop 160).take 8 = data160

numeric_data_binding piece160 : data160 = ((originalEntries.drop 160).take 8).map NumericFunctionalBaseChecks.encode

theorem binding160 : (data.drop 160).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 160).take 8 :=
  view160.trans (piece160.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 160 8))

numeric_data_binding view168 : (data.drop 168).take 8 = data168

numeric_data_binding piece168 : data168 = ((originalEntries.drop 168).take 8).map NumericFunctionalBaseChecks.encode

theorem binding168 : (data.drop 168).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 168).take 8 :=
  view168.trans (piece168.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 168 8))

numeric_data_binding view176 : (data.drop 176).take 8 = data176

numeric_data_binding piece176 : data176 = ((originalEntries.drop 176).take 8).map NumericFunctionalBaseChecks.encode

theorem binding176 : (data.drop 176).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 176).take 8 :=
  view176.trans (piece176.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 176 8))

numeric_data_binding view184 : (data.drop 184).take 8 = data184

numeric_data_binding piece184 : data184 = ((originalEntries.drop 184).take 8).map NumericFunctionalBaseChecks.encode

theorem binding184 : (data.drop 184).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 184).take 8 :=
  view184.trans (piece184.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 184 8))

numeric_data_binding view192 : (data.drop 192).take 8 = data192

numeric_data_binding piece192 : data192 = ((originalEntries.drop 192).take 8).map NumericFunctionalBaseChecks.encode

theorem binding192 : (data.drop 192).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 192).take 8 :=
  view192.trans (piece192.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 192 8))

numeric_data_binding view200 : (data.drop 200).take 8 = data200

numeric_data_binding piece200 : data200 = ((originalEntries.drop 200).take 8).map NumericFunctionalBaseChecks.encode

theorem binding200 : (data.drop 200).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 200).take 8 :=
  view200.trans (piece200.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 200 8))

numeric_data_binding view208 : (data.drop 208).take 8 = data208

numeric_data_binding piece208 : data208 = ((originalEntries.drop 208).take 8).map NumericFunctionalBaseChecks.encode

theorem binding208 : (data.drop 208).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 208).take 8 :=
  view208.trans (piece208.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 208 8))

numeric_data_binding view216 : (data.drop 216).take 8 = data216

numeric_data_binding piece216 : data216 = ((originalEntries.drop 216).take 8).map NumericFunctionalBaseChecks.encode

theorem binding216 : (data.drop 216).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 216).take 8 :=
  view216.trans (piece216.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 216 8))

numeric_data_binding view224 : (data.drop 224).take 8 = data224

numeric_data_binding piece224 : data224 = ((originalEntries.drop 224).take 8).map NumericFunctionalBaseChecks.encode

theorem binding224 : (data.drop 224).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 224).take 8 :=
  view224.trans (piece224.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 224 8))

numeric_data_binding view232 : (data.drop 232).take 8 = data232

numeric_data_binding piece232 : data232 = ((originalEntries.drop 232).take 8).map NumericFunctionalBaseChecks.encode

theorem binding232 : (data.drop 232).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 232).take 8 :=
  view232.trans (piece232.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 232 8))

numeric_data_binding view240 : (data.drop 240).take 8 = data240

numeric_data_binding piece240 : data240 = ((originalEntries.drop 240).take 8).map NumericFunctionalBaseChecks.encode

theorem binding240 : (data.drop 240).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 240).take 8 :=
  view240.trans (piece240.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 240 8))

numeric_data_binding view248 : (data.drop 248).take 8 = data248

numeric_data_binding piece248 : data248 = ((originalEntries.drop 248).take 8).map NumericFunctionalBaseChecks.encode

theorem binding248 : (data.drop 248).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 248).take 8 :=
  view248.trans (piece248.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 248 8))

numeric_data_binding view256 : (data.drop 256).take 8 = data256

numeric_data_binding piece256 : data256 = ((originalEntries.drop 256).take 8).map NumericFunctionalBaseChecks.encode

theorem binding256 : (data.drop 256).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 256).take 8 :=
  view256.trans (piece256.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 256 8))

numeric_data_binding view264 : (data.drop 264).take 8 = data264

numeric_data_binding piece264 : data264 = ((originalEntries.drop 264).take 8).map NumericFunctionalBaseChecks.encode

theorem binding264 : (data.drop 264).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 264).take 8 :=
  view264.trans (piece264.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 264 8))

numeric_data_binding view272 : (data.drop 272).take 8 = data272

numeric_data_binding piece272 : data272 = ((originalEntries.drop 272).take 8).map NumericFunctionalBaseChecks.encode

theorem binding272 : (data.drop 272).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 272).take 8 :=
  view272.trans (piece272.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 272 8))

numeric_data_binding view280 : (data.drop 280).take 8 = data280

numeric_data_binding piece280 : data280 = ((originalEntries.drop 280).take 8).map NumericFunctionalBaseChecks.encode

theorem binding280 : (data.drop 280).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 280).take 8 :=
  view280.trans (piece280.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 280 8))

numeric_data_binding view288 : (data.drop 288).take 8 = data288

numeric_data_binding piece288 : data288 = ((originalEntries.drop 288).take 8).map NumericFunctionalBaseChecks.encode

theorem binding288 : (data.drop 288).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 288).take 8 :=
  view288.trans (piece288.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 288 8))

numeric_data_binding view296 : (data.drop 296).take 8 = data296

numeric_data_binding piece296 : data296 = ((originalEntries.drop 296).take 8).map NumericFunctionalBaseChecks.encode

theorem binding296 : (data.drop 296).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 296).take 8 :=
  view296.trans (piece296.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 296 8))

numeric_data_binding view304 : (data.drop 304).take 8 = data304

numeric_data_binding piece304 : data304 = ((originalEntries.drop 304).take 8).map NumericFunctionalBaseChecks.encode

theorem binding304 : (data.drop 304).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 304).take 8 :=
  view304.trans (piece304.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 304 8))

numeric_data_binding view312 : (data.drop 312).take 8 = data312

numeric_data_binding piece312 : data312 = ((originalEntries.drop 312).take 8).map NumericFunctionalBaseChecks.encode

theorem binding312 : (data.drop 312).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 312).take 8 :=
  view312.trans (piece312.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 312 8))

numeric_data_binding view320 : (data.drop 320).take 8 = data320

numeric_data_binding piece320 : data320 = ((originalEntries.drop 320).take 8).map NumericFunctionalBaseChecks.encode

theorem binding320 : (data.drop 320).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 320).take 8 :=
  view320.trans (piece320.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 320 8))

numeric_data_binding view328 : (data.drop 328).take 8 = data328

numeric_data_binding piece328 : data328 = ((originalEntries.drop 328).take 8).map NumericFunctionalBaseChecks.encode

theorem binding328 : (data.drop 328).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 328).take 8 :=
  view328.trans (piece328.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 328 8))

numeric_data_binding view336 : (data.drop 336).take 8 = data336

numeric_data_binding piece336 : data336 = ((originalEntries.drop 336).take 8).map NumericFunctionalBaseChecks.encode

theorem binding336 : (data.drop 336).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 336).take 8 :=
  view336.trans (piece336.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 336 8))

numeric_data_binding view344 : (data.drop 344).take 8 = data344

numeric_data_binding piece344 : data344 = ((originalEntries.drop 344).take 8).map NumericFunctionalBaseChecks.encode

theorem binding344 : (data.drop 344).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 344).take 8 :=
  view344.trans (piece344.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 344 8))

numeric_data_binding view352 : (data.drop 352).take 8 = data352

numeric_data_binding piece352 : data352 = ((originalEntries.drop 352).take 8).map NumericFunctionalBaseChecks.encode

theorem binding352 : (data.drop 352).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 352).take 8 :=
  view352.trans (piece352.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 352 8))

numeric_data_binding view360 : (data.drop 360).take 8 = data360

numeric_data_binding piece360 : data360 = ((originalEntries.drop 360).take 8).map NumericFunctionalBaseChecks.encode

theorem binding360 : (data.drop 360).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 360).take 8 :=
  view360.trans (piece360.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 360 8))

numeric_data_binding view368 : (data.drop 368).take 8 = data368

numeric_data_binding piece368 : data368 = ((originalEntries.drop 368).take 8).map NumericFunctionalBaseChecks.encode

theorem binding368 : (data.drop 368).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 368).take 8 :=
  view368.trans (piece368.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 368 8))

numeric_data_binding view376 : (data.drop 376).take 8 = data376

numeric_data_binding piece376 : data376 = ((originalEntries.drop 376).take 8).map NumericFunctionalBaseChecks.encode

theorem binding376 : (data.drop 376).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 376).take 8 :=
  view376.trans (piece376.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 376 8))

numeric_data_binding view384 : (data.drop 384).take 8 = data384

numeric_data_binding piece384 : data384 = ((originalEntries.drop 384).take 8).map NumericFunctionalBaseChecks.encode

theorem binding384 : (data.drop 384).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 384).take 8 :=
  view384.trans (piece384.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 384 8))

numeric_data_binding view392 : (data.drop 392).take 8 = data392

numeric_data_binding piece392 : data392 = ((originalEntries.drop 392).take 8).map NumericFunctionalBaseChecks.encode

theorem binding392 : (data.drop 392).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 392).take 8 :=
  view392.trans (piece392.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 392 8))

numeric_data_binding view400 : (data.drop 400).take 8 = data400

numeric_data_binding piece400 : data400 = ((originalEntries.drop 400).take 8).map NumericFunctionalBaseChecks.encode

theorem binding400 : (data.drop 400).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 400).take 8 :=
  view400.trans (piece400.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 400 8))

numeric_data_binding view408 : (data.drop 408).take 8 = data408

numeric_data_binding piece408 : data408 = ((originalEntries.drop 408).take 8).map NumericFunctionalBaseChecks.encode

theorem binding408 : (data.drop 408).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 408).take 8 :=
  view408.trans (piece408.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 408 8))

numeric_data_binding view416 : (data.drop 416).take 8 = data416

numeric_data_binding piece416 : data416 = ((originalEntries.drop 416).take 8).map NumericFunctionalBaseChecks.encode

theorem binding416 : (data.drop 416).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 416).take 8 :=
  view416.trans (piece416.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 416 8))

numeric_data_binding view424 : (data.drop 424).take 8 = data424

numeric_data_binding piece424 : data424 = ((originalEntries.drop 424).take 8).map NumericFunctionalBaseChecks.encode

theorem binding424 : (data.drop 424).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 424).take 8 :=
  view424.trans (piece424.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 424 8))

numeric_data_binding view432 : (data.drop 432).take 8 = data432

numeric_data_binding piece432 : data432 = ((originalEntries.drop 432).take 8).map NumericFunctionalBaseChecks.encode

theorem binding432 : (data.drop 432).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 432).take 8 :=
  view432.trans (piece432.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 432 8))

numeric_data_binding view440 : (data.drop 440).take 8 = data440

numeric_data_binding piece440 : data440 = ((originalEntries.drop 440).take 8).map NumericFunctionalBaseChecks.encode

theorem binding440 : (data.drop 440).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 440).take 8 :=
  view440.trans (piece440.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 440 8))

numeric_data_binding view448 : (data.drop 448).take 8 = data448

numeric_data_binding piece448 : data448 = ((originalEntries.drop 448).take 8).map NumericFunctionalBaseChecks.encode

theorem binding448 : (data.drop 448).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 448).take 8 :=
  view448.trans (piece448.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 448 8))

numeric_data_binding view456 : (data.drop 456).take 8 = data456

numeric_data_binding piece456 : data456 = ((originalEntries.drop 456).take 8).map NumericFunctionalBaseChecks.encode

theorem binding456 : (data.drop 456).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 456).take 8 :=
  view456.trans (piece456.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 456 8))

numeric_data_binding view464 : (data.drop 464).take 8 = data464

numeric_data_binding piece464 : data464 = ((originalEntries.drop 464).take 8).map NumericFunctionalBaseChecks.encode

theorem binding464 : (data.drop 464).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 464).take 8 :=
  view464.trans (piece464.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 464 8))

numeric_data_binding view472 : (data.drop 472).take 8 = data472

numeric_data_binding piece472 : data472 = ((originalEntries.drop 472).take 8).map NumericFunctionalBaseChecks.encode

theorem binding472 : (data.drop 472).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 472).take 8 :=
  view472.trans (piece472.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 472 8))

numeric_data_binding view480 : (data.drop 480).take 8 = data480

numeric_data_binding piece480 : data480 = ((originalEntries.drop 480).take 8).map NumericFunctionalBaseChecks.encode

theorem binding480 : (data.drop 480).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 480).take 8 :=
  view480.trans (piece480.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 480 8))

numeric_data_binding view488 : (data.drop 488).take 8 = data488

numeric_data_binding piece488 : data488 = ((originalEntries.drop 488).take 8).map NumericFunctionalBaseChecks.encode

theorem binding488 : (data.drop 488).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 488).take 8 :=
  view488.trans (piece488.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 488 8))

numeric_data_binding view496 : (data.drop 496).take 8 = data496

numeric_data_binding piece496 : data496 = ((originalEntries.drop 496).take 8).map NumericFunctionalBaseChecks.encode

theorem binding496 : (data.drop 496).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 496).take 8 :=
  view496.trans (piece496.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 496 8))

numeric_data_binding view504 : (data.drop 504).take 8 = data504

numeric_data_binding piece504 : data504 = ((originalEntries.drop 504).take 8).map NumericFunctionalBaseChecks.encode

theorem binding504 : (data.drop 504).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 504).take 8 :=
  view504.trans (piece504.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 504 8))

numeric_data_binding view512 : (data.drop 512).take 8 = data512

numeric_data_binding piece512 : data512 = ((originalEntries.drop 512).take 8).map NumericFunctionalBaseChecks.encode

theorem binding512 : (data.drop 512).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 512).take 8 :=
  view512.trans (piece512.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 512 8))

numeric_data_binding view520 : (data.drop 520).take 8 = data520

numeric_data_binding piece520 : data520 = ((originalEntries.drop 520).take 8).map NumericFunctionalBaseChecks.encode

theorem binding520 : (data.drop 520).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 520).take 8 :=
  view520.trans (piece520.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 520 8))

numeric_data_binding view528 : (data.drop 528).take 8 = data528

numeric_data_binding piece528 : data528 = ((originalEntries.drop 528).take 8).map NumericFunctionalBaseChecks.encode

theorem binding528 : (data.drop 528).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 528).take 8 :=
  view528.trans (piece528.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 528 8))

numeric_data_binding view536 : (data.drop 536).take 8 = data536

numeric_data_binding piece536 : data536 = ((originalEntries.drop 536).take 8).map NumericFunctionalBaseChecks.encode

theorem binding536 : (data.drop 536).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 536).take 8 :=
  view536.trans (piece536.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 536 8))

numeric_data_binding view544 : (data.drop 544).take 8 = data544

numeric_data_binding piece544 : data544 = ((originalEntries.drop 544).take 8).map NumericFunctionalBaseChecks.encode

theorem binding544 : (data.drop 544).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 544).take 8 :=
  view544.trans (piece544.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 544 8))

numeric_data_binding view552 : (data.drop 552).take 8 = data552

numeric_data_binding piece552 : data552 = ((originalEntries.drop 552).take 8).map NumericFunctionalBaseChecks.encode

theorem binding552 : (data.drop 552).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 552).take 8 :=
  view552.trans (piece552.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 552 8))

numeric_data_binding view560 : (data.drop 560).take 8 = data560

numeric_data_binding piece560 : data560 = ((originalEntries.drop 560).take 8).map NumericFunctionalBaseChecks.encode

theorem binding560 : (data.drop 560).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 560).take 8 :=
  view560.trans (piece560.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 560 8))

numeric_data_binding view568 : (data.drop 568).take 8 = data568

numeric_data_binding piece568 : data568 = ((originalEntries.drop 568).take 8).map NumericFunctionalBaseChecks.encode

theorem binding568 : (data.drop 568).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 568).take 8 :=
  view568.trans (piece568.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 568 8))

numeric_data_binding view576 : (data.drop 576).take 8 = data576

numeric_data_binding piece576 : data576 = ((originalEntries.drop 576).take 8).map NumericFunctionalBaseChecks.encode

theorem binding576 : (data.drop 576).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 576).take 8 :=
  view576.trans (piece576.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 576 8))

numeric_data_binding view584 : (data.drop 584).take 8 = data584

numeric_data_binding piece584 : data584 = ((originalEntries.drop 584).take 8).map NumericFunctionalBaseChecks.encode

theorem binding584 : (data.drop 584).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 584).take 8 :=
  view584.trans (piece584.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 584 8))

numeric_data_binding view592 : (data.drop 592).take 8 = data592

numeric_data_binding piece592 : data592 = ((originalEntries.drop 592).take 8).map NumericFunctionalBaseChecks.encode

theorem binding592 : (data.drop 592).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 592).take 8 :=
  view592.trans (piece592.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 592 8))

numeric_data_binding view600 : (data.drop 600).take 8 = data600

numeric_data_binding piece600 : data600 = ((originalEntries.drop 600).take 8).map NumericFunctionalBaseChecks.encode

theorem binding600 : (data.drop 600).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 600).take 8 :=
  view600.trans (piece600.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 600 8))

numeric_data_binding view608 : (data.drop 608).take 8 = data608

numeric_data_binding piece608 : data608 = ((originalEntries.drop 608).take 8).map NumericFunctionalBaseChecks.encode

theorem binding608 : (data.drop 608).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 608).take 8 :=
  view608.trans (piece608.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 608 8))

numeric_data_binding view616 : (data.drop 616).take 8 = data616

numeric_data_binding piece616 : data616 = ((originalEntries.drop 616).take 8).map NumericFunctionalBaseChecks.encode

theorem binding616 : (data.drop 616).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 616).take 8 :=
  view616.trans (piece616.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 616 8))

numeric_data_binding view624 : (data.drop 624).take 8 = data624

numeric_data_binding piece624 : data624 = ((originalEntries.drop 624).take 8).map NumericFunctionalBaseChecks.encode

theorem binding624 : (data.drop 624).take 8 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 624).take 8 :=
  view624.trans (piece624.trans (NumericQueryFrameChecks.map_window originalEntries NumericFunctionalBaseChecks.encode 624 8))

theorem sourceNode0_16 : (data.drop 0).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 8 8 binding0 binding8

theorem sourceNode16_16 : (data.drop 16).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 16).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 16 8 8 binding16 binding24

theorem sourceNode0_32 : (data.drop 0).take 32 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 32 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 16 16 sourceNode0_16 sourceNode16_16

theorem sourceNode32_16 : (data.drop 32).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 32).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 32 8 8 binding32 binding40

theorem sourceNode56_16 : (data.drop 56).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 56).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 56 8 8 binding56 binding64

theorem sourceNode48_24 : (data.drop 48).take 24 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 48).take 24 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 48 8 16 binding48 sourceNode56_16

theorem sourceNode32_40 : (data.drop 32).take 40 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 32).take 40 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 32 16 24 sourceNode32_16 sourceNode48_24

theorem sourceNode0_72 : (data.drop 0).take 72 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 72 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 32 40 sourceNode0_32 sourceNode32_40

theorem sourceNode72_16 : (data.drop 72).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 72).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 72 8 8 binding72 binding80

theorem sourceNode96_16 : (data.drop 96).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 96).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 96 8 8 binding96 binding104

theorem sourceNode88_24 : (data.drop 88).take 24 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 88).take 24 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 88 8 16 binding88 sourceNode96_16

theorem sourceNode72_40 : (data.drop 72).take 40 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 72).take 40 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 72 16 24 sourceNode72_16 sourceNode88_24

theorem sourceNode112_16 : (data.drop 112).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 112).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 112 8 8 binding112 binding120

theorem sourceNode136_16 : (data.drop 136).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 136).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 136 8 8 binding136 binding144

theorem sourceNode128_24 : (data.drop 128).take 24 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 128).take 24 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 128 8 16 binding128 sourceNode136_16

theorem sourceNode112_40 : (data.drop 112).take 40 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 112).take 40 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 112 16 24 sourceNode112_16 sourceNode128_24

theorem sourceNode72_80 : (data.drop 72).take 80 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 72).take 80 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 72 40 40 sourceNode72_40 sourceNode112_40

theorem sourceNode0_152 : (data.drop 0).take 152 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 152 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 72 80 sourceNode0_72 sourceNode72_80

theorem sourceNode152_16 : (data.drop 152).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 152).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 152 8 8 binding152 binding160

theorem sourceNode176_16 : (data.drop 176).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 176).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 176 8 8 binding176 binding184

theorem sourceNode168_24 : (data.drop 168).take 24 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 168).take 24 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 168 8 16 binding168 sourceNode176_16

theorem sourceNode152_40 : (data.drop 152).take 40 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 152).take 40 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 152 16 24 sourceNode152_16 sourceNode168_24

theorem sourceNode192_16 : (data.drop 192).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 192).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 192 8 8 binding192 binding200

theorem sourceNode216_16 : (data.drop 216).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 216).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 216 8 8 binding216 binding224

theorem sourceNode208_24 : (data.drop 208).take 24 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 208).take 24 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 208 8 16 binding208 sourceNode216_16

theorem sourceNode192_40 : (data.drop 192).take 40 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 192).take 40 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 192 16 24 sourceNode192_16 sourceNode208_24

theorem sourceNode152_80 : (data.drop 152).take 80 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 152).take 80 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 152 40 40 sourceNode152_40 sourceNode192_40

theorem sourceNode232_16 : (data.drop 232).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 232).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 232 8 8 binding232 binding240

theorem sourceNode256_16 : (data.drop 256).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 256).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 256 8 8 binding256 binding264

theorem sourceNode248_24 : (data.drop 248).take 24 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 248).take 24 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 248 8 16 binding248 sourceNode256_16

theorem sourceNode232_40 : (data.drop 232).take 40 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 232).take 40 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 232 16 24 sourceNode232_16 sourceNode248_24

theorem sourceNode272_16 : (data.drop 272).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 272).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 272 8 8 binding272 binding280

theorem sourceNode296_16 : (data.drop 296).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 296).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 296 8 8 binding296 binding304

theorem sourceNode288_24 : (data.drop 288).take 24 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 288).take 24 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 288 8 16 binding288 sourceNode296_16

theorem sourceNode272_40 : (data.drop 272).take 40 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 272).take 40 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 272 16 24 sourceNode272_16 sourceNode288_24

theorem sourceNode232_80 : (data.drop 232).take 80 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 232).take 80 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 232 40 40 sourceNode232_40 sourceNode272_40

theorem sourceNode152_160 : (data.drop 152).take 160 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 152).take 160 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 152 80 80 sourceNode152_80 sourceNode232_80

theorem sourceNode0_312 : (data.drop 0).take 312 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 312 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 152 160 sourceNode0_152 sourceNode152_160

theorem sourceNode312_16 : (data.drop 312).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 312).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 312 8 8 binding312 binding320

theorem sourceNode336_16 : (data.drop 336).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 336).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 336 8 8 binding336 binding344

theorem sourceNode328_24 : (data.drop 328).take 24 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 328).take 24 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 328 8 16 binding328 sourceNode336_16

theorem sourceNode312_40 : (data.drop 312).take 40 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 312).take 40 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 312 16 24 sourceNode312_16 sourceNode328_24

theorem sourceNode352_16 : (data.drop 352).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 352).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 352 8 8 binding352 binding360

theorem sourceNode376_16 : (data.drop 376).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 376).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 376 8 8 binding376 binding384

theorem sourceNode368_24 : (data.drop 368).take 24 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 368).take 24 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 368 8 16 binding368 sourceNode376_16

theorem sourceNode352_40 : (data.drop 352).take 40 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 352).take 40 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 352 16 24 sourceNode352_16 sourceNode368_24

theorem sourceNode312_80 : (data.drop 312).take 80 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 312).take 80 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 312 40 40 sourceNode312_40 sourceNode352_40

theorem sourceNode392_16 : (data.drop 392).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 392).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 392 8 8 binding392 binding400

theorem sourceNode416_16 : (data.drop 416).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 416).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 416 8 8 binding416 binding424

theorem sourceNode408_24 : (data.drop 408).take 24 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 408).take 24 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 408 8 16 binding408 sourceNode416_16

theorem sourceNode392_40 : (data.drop 392).take 40 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 392).take 40 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 392 16 24 sourceNode392_16 sourceNode408_24

theorem sourceNode432_16 : (data.drop 432).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 432).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 432 8 8 binding432 binding440

theorem sourceNode456_16 : (data.drop 456).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 456).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 456 8 8 binding456 binding464

theorem sourceNode448_24 : (data.drop 448).take 24 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 448).take 24 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 448 8 16 binding448 sourceNode456_16

theorem sourceNode432_40 : (data.drop 432).take 40 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 432).take 40 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 432 16 24 sourceNode432_16 sourceNode448_24

theorem sourceNode392_80 : (data.drop 392).take 80 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 392).take 80 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 392 40 40 sourceNode392_40 sourceNode432_40

theorem sourceNode312_160 : (data.drop 312).take 160 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 312).take 160 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 312 80 80 sourceNode312_80 sourceNode392_80

theorem sourceNode472_16 : (data.drop 472).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 472).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 472 8 8 binding472 binding480

theorem sourceNode496_16 : (data.drop 496).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 496).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 496 8 8 binding496 binding504

theorem sourceNode488_24 : (data.drop 488).take 24 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 488).take 24 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 488 8 16 binding488 sourceNode496_16

theorem sourceNode472_40 : (data.drop 472).take 40 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 472).take 40 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 472 16 24 sourceNode472_16 sourceNode488_24

theorem sourceNode512_16 : (data.drop 512).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 512).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 512 8 8 binding512 binding520

theorem sourceNode536_16 : (data.drop 536).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 536).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 536 8 8 binding536 binding544

theorem sourceNode528_24 : (data.drop 528).take 24 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 528).take 24 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 528 8 16 binding528 sourceNode536_16

theorem sourceNode512_40 : (data.drop 512).take 40 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 512).take 40 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 512 16 24 sourceNode512_16 sourceNode528_24

theorem sourceNode472_80 : (data.drop 472).take 80 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 472).take 80 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 472 40 40 sourceNode472_40 sourceNode512_40

theorem sourceNode552_16 : (data.drop 552).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 552).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 552 8 8 binding552 binding560

theorem sourceNode576_16 : (data.drop 576).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 576).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 576 8 8 binding576 binding584

theorem sourceNode568_24 : (data.drop 568).take 24 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 568).take 24 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 568 8 16 binding568 sourceNode576_16

theorem sourceNode552_40 : (data.drop 552).take 40 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 552).take 40 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 552 16 24 sourceNode552_16 sourceNode568_24

theorem sourceNode592_16 : (data.drop 592).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 592).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 592 8 8 binding592 binding600

theorem sourceNode616_16 : (data.drop 616).take 16 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 616).take 16 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 616 8 8 binding616 binding624

theorem sourceNode608_24 : (data.drop 608).take 24 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 608).take 24 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 608 8 16 binding608 sourceNode616_16

theorem sourceNode592_40 : (data.drop 592).take 40 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 592).take 40 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 592 16 24 sourceNode592_16 sourceNode608_24

theorem sourceNode552_80 : (data.drop 552).take 80 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 552).take 80 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 552 40 40 sourceNode552_40 sourceNode592_40

theorem sourceNode472_160 : (data.drop 472).take 160 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 472).take 160 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 472 80 80 sourceNode472_80 sourceNode552_80

theorem sourceNode312_320 : (data.drop 312).take 320 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 312).take 320 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 312 160 160 sourceNode312_160 sourceNode472_160

theorem sourceNode0_632 : (data.drop 0).take 632 = ((originalEntries.map NumericFunctionalBaseChecks.encode).drop 0).take 632 :=
  NumericQueryFrameChecks.merge_bindings data (originalEntries.map NumericFunctionalBaseChecks.encode) 0 312 320 sourceNode0_312 sourceNode312_320

theorem raw_binding : data = originalEntries.map NumericFunctionalBaseChecks.encode :=
  NumericQueryFrameChecks.complete_binding data (originalEntries.map NumericFunctionalBaseChecks.encode) 632
    (by decide +kernel) (by decide +kernel) sourceNode0_632

theorem source_binding : data = NumericSourceFreshnessChecks.encodeAddresses sourceAddresses := by
  simpa only [originalEntries, NumericSourceFreshnessChecks.encodeAddresses, List.map_map, Function.comp_def] using raw_binding

numeric_data_binding target_binding : targetData = NumericSourceFreshnessChecks.encodeAddresses targetAddresses

end Airbender.Compiler.SourceFreshnessChecks.BlakeRoundCached
