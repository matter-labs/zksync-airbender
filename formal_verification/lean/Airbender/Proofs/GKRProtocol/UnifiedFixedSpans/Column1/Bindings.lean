import Airbender.Proofs.GKRProtocol.UnifiedFixedSpans.Column1.Codes
import Airbender.Import.GKRProtocol.NumericArithmeticDataImport

namespace Airbender.Compiler.UnifiedFixedSpans.Column1
open Airbender Airbender.Compiler
open PackedSetupEquality
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072

numeric_data_binding source0_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.source0 = (source0.get ⟨0, by decide +kernel⟩).decode
numeric_data_binding targets0_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.target0 = targets0.map BlockCode.decode
numeric_data_binding source1_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.source1 = (source1.get ⟨0, by decide +kernel⟩).decode
numeric_data_binding targets1_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.target1 = targets1.map BlockCode.decode
numeric_data_binding source2_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.source2 = (source2.get ⟨0, by decide +kernel⟩).decode
numeric_data_binding targets2_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.target2 = targets2.map BlockCode.decode
numeric_data_binding source3_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.source3 = (source3.get ⟨0, by decide +kernel⟩).decode
numeric_data_binding targets3_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.target3 = targets3.map BlockCode.decode
numeric_data_binding source4_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.source4 = (source4.get ⟨0, by decide +kernel⟩).decode
numeric_data_binding targets4_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.target4 = targets4.map BlockCode.decode
numeric_data_binding source5_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.source5 = (source5.get ⟨0, by decide +kernel⟩).decode
numeric_data_binding targets5_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.target5 = targets5.map BlockCode.decode
numeric_data_binding source6_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.source6 = (source6.get ⟨0, by decide +kernel⟩).decode
numeric_data_binding targets6_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.target6 = targets6.map BlockCode.decode
numeric_data_binding source7_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.source7 = (source7.get ⟨0, by decide +kernel⟩).decode
numeric_data_binding targets7_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.target7 = targets7.map BlockCode.decode
numeric_data_binding source8_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.source8 = (source8.get ⟨0, by decide +kernel⟩).decode
numeric_data_binding targets8_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.target8 = targets8.map BlockCode.decode
numeric_data_binding source9_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.source9 = (source9.get ⟨0, by decide +kernel⟩).decode
numeric_data_binding targets9_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.target9 = targets9.map BlockCode.decode
numeric_data_binding source10_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.source10 = (source10.get ⟨0, by decide +kernel⟩).decode
numeric_data_binding targets10_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.target10 = targets10.map BlockCode.decode
numeric_data_binding source11_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.source11 = (source11.get ⟨0, by decide +kernel⟩).decode
numeric_data_binding targets11_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.target11 = targets11.map BlockCode.decode
numeric_data_binding source15_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.source15 = (source15.get ⟨0, by decide +kernel⟩).decode
numeric_data_binding targets15_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.target15 = targets15.map BlockCode.decode
numeric_data_binding source16_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.source16 = (source16.get ⟨0, by decide +kernel⟩).decode
numeric_data_binding targets16_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.target16 = targets16.map BlockCode.decode
numeric_data_binding source17_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.source17 = (source17.get ⟨0, by decide +kernel⟩).decode
numeric_data_binding targets17_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.target17 = targets17.map BlockCode.decode
numeric_data_binding source18_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.source18 = (source18.get ⟨0, by decide +kernel⟩).decode
numeric_data_binding targets18_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.target18 = targets18.map BlockCode.decode
numeric_data_binding source19_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.source19 = (source19.get ⟨0, by decide +kernel⟩).decode
numeric_data_binding targets19_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.target19 = targets19.map BlockCode.decode
numeric_data_binding source20_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.source20 = (source20.get ⟨0, by decide +kernel⟩).decode
numeric_data_binding targets20_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.target20 = targets20.map BlockCode.decode
numeric_data_binding source21_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.source21 = (source21.get ⟨0, by decide +kernel⟩).decode
numeric_data_binding targets21_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.target21 = targets21.map BlockCode.decode
numeric_data_binding source22_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.source22 = (source22.get ⟨0, by decide +kernel⟩).decode
numeric_data_binding targets22_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.target22 = targets22.map BlockCode.decode
numeric_data_binding source23_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.source23 = (source23.get ⟨0, by decide +kernel⟩).decode
numeric_data_binding targets23_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.target23 = targets23.map BlockCode.decode
numeric_data_binding source24_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.source24 = (source24.get ⟨0, by decide +kernel⟩).decode
numeric_data_binding targets24_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.target24 = targets24.map BlockCode.decode
numeric_data_binding source25_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.source25 = (source25.get ⟨0, by decide +kernel⟩).decode
numeric_data_binding targets25_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.target25 = targets25.map BlockCode.decode
numeric_data_binding source26_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.source26 = (source26.get ⟨0, by decide +kernel⟩).decode
numeric_data_binding targets26_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.target26 = targets26.map BlockCode.decode
numeric_data_binding source27_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.source27 = (source27.get ⟨0, by decide +kernel⟩).decode
numeric_data_binding targets27_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.target27 = targets27.map BlockCode.decode
numeric_data_binding source28_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.source28 = (source28.get ⟨0, by decide +kernel⟩).decode
numeric_data_binding targets28_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.target28 = targets28.map BlockCode.decode
numeric_data_binding source29_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.source29 = (source29.get ⟨0, by decide +kernel⟩).decode
numeric_data_binding targets29_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.target29 = targets29.map BlockCode.decode
numeric_data_binding source30_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.source30 = (source30.get ⟨0, by decide +kernel⟩).decode
numeric_data_binding targets30_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.target30 = targets30.map BlockCode.decode
numeric_data_binding source31_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.source31 = (source31.get ⟨0, by decide +kernel⟩).decode
numeric_data_binding targets31_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.target31 = targets31.map BlockCode.decode
numeric_data_binding source32_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.source32 = (source32.get ⟨0, by decide +kernel⟩).decode
numeric_data_binding targets32_binding : Airbender.Compiler.UnifiedPrefixNative.Column1.target32 = targets32.map BlockCode.decode

end Airbender.Compiler.UnifiedFixedSpans.Column1
