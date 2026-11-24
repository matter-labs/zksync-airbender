module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.CleanIdealNative.BlakeRoundCachedData
public import Proven.GKRProtocol.CleanIdealRows
public import Proven.Import.GKRProtocol.NumericArithmeticDataImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.CleanIdealNative.BlakeRoundCached
set_option maxRecDepth 32768

def rowCapture : CleanIdealRows.Capture := ⟨capture, expanded, combinations⟩
numeric_data_binding expanded_binding0 : codes0.map (NumericExpressionChecks.Code.polynomial babyBearModulus) = expanded0
numeric_data_binding expanded_binding1 : codes1.map (NumericExpressionChecks.Code.polynomial babyBearModulus) = expanded1
numeric_data_binding expanded_binding2 : codes2.map (NumericExpressionChecks.Code.polynomial babyBearModulus) = expanded2
numeric_data_binding expanded_binding3 : codes3.map (NumericExpressionChecks.Code.polynomial babyBearModulus) = expanded3
numeric_data_binding expanded_binding4 : codes4.map (NumericExpressionChecks.Code.polynomial babyBearModulus) = expanded4
numeric_data_binding expanded_binding5 : codes5.map (NumericExpressionChecks.Code.polynomial babyBearModulus) = expanded5
numeric_data_binding expanded_binding6 : codes6.map (NumericExpressionChecks.Code.polynomial babyBearModulus) = expanded6
numeric_data_binding expanded_binding7 : codes7.map (NumericExpressionChecks.Code.polynomial babyBearModulus) = expanded7
numeric_data_binding expanded_binding8 : codes8.map (NumericExpressionChecks.Code.polynomial babyBearModulus) = expanded8
numeric_data_binding expanded_binding9 : codes9.map (NumericExpressionChecks.Code.polynomial babyBearModulus) = expanded9
numeric_data_binding expanded_binding10 : codes10.map (NumericExpressionChecks.Code.polynomial babyBearModulus) = expanded10
numeric_data_binding expanded_binding11 : codes11.map (NumericExpressionChecks.Code.polynomial babyBearModulus) = expanded11
numeric_data_binding expanded_binding12 : codes12.map (NumericExpressionChecks.Code.polynomial babyBearModulus) = expanded12
numeric_data_binding expanded_binding13 : codes13.map (NumericExpressionChecks.Code.polynomial babyBearModulus) = expanded13
theorem expanded_binding : CleanIdealChecks.mapTable (NumericExpressionChecks.Code.polynomial babyBearModulus) codes = expanded :=
  (congrArg₂ (NumericPolynomialChecks.LookupTable.branch 112) (congrArg₂ (NumericPolynomialChecks.LookupTable.branch 48) (congrArg₂ (NumericPolynomialChecks.LookupTable.branch 16) (congrArg NumericPolynomialChecks.LookupTable.leaf expanded_binding0) (congrArg₂ (NumericPolynomialChecks.LookupTable.branch 16) (congrArg NumericPolynomialChecks.LookupTable.leaf expanded_binding1) (congrArg NumericPolynomialChecks.LookupTable.leaf expanded_binding2))) (congrArg₂ (NumericPolynomialChecks.LookupTable.branch 32) (congrArg₂ (NumericPolynomialChecks.LookupTable.branch 16) (congrArg NumericPolynomialChecks.LookupTable.leaf expanded_binding3) (congrArg NumericPolynomialChecks.LookupTable.leaf expanded_binding4)) (congrArg₂ (NumericPolynomialChecks.LookupTable.branch 16) (congrArg NumericPolynomialChecks.LookupTable.leaf expanded_binding5) (congrArg NumericPolynomialChecks.LookupTable.leaf expanded_binding6)))) (congrArg₂ (NumericPolynomialChecks.LookupTable.branch 48) (congrArg₂ (NumericPolynomialChecks.LookupTable.branch 16) (congrArg NumericPolynomialChecks.LookupTable.leaf expanded_binding7) (congrArg₂ (NumericPolynomialChecks.LookupTable.branch 16) (congrArg NumericPolynomialChecks.LookupTable.leaf expanded_binding8) (congrArg NumericPolynomialChecks.LookupTable.leaf expanded_binding9))) (congrArg₂ (NumericPolynomialChecks.LookupTable.branch 32) (congrArg₂ (NumericPolynomialChecks.LookupTable.branch 16) (congrArg NumericPolynomialChecks.LookupTable.leaf expanded_binding10) (congrArg NumericPolynomialChecks.LookupTable.leaf expanded_binding11)) (congrArg₂ (NumericPolynomialChecks.LookupTable.branch 16) (congrArg NumericPolynomialChecks.LookupTable.leaf expanded_binding12) (congrArg NumericPolynomialChecks.LookupTable.leaf expanded_binding13)))))

numeric_data_binding combinations_binding0 : witnesses0.map (NumericArithmeticChecks.combine babyBearModulus relations) = combinations0
numeric_data_binding combinations_binding1 : witnesses1.map (NumericArithmeticChecks.combine babyBearModulus relations) = combinations1
numeric_data_binding combinations_binding2 : witnesses2.map (NumericArithmeticChecks.combine babyBearModulus relations) = combinations2
numeric_data_binding combinations_binding3 : witnesses3.map (NumericArithmeticChecks.combine babyBearModulus relations) = combinations3
numeric_data_binding combinations_binding4 : witnesses4.map (NumericArithmeticChecks.combine babyBearModulus relations) = combinations4
numeric_data_binding combinations_binding5 : witnesses5.map (NumericArithmeticChecks.combine babyBearModulus relations) = combinations5
numeric_data_binding combinations_binding6 : witnesses6.map (NumericArithmeticChecks.combine babyBearModulus relations) = combinations6
numeric_data_binding combinations_binding7 : witnesses7.map (NumericArithmeticChecks.combine babyBearModulus relations) = combinations7
numeric_data_binding combinations_binding8 : witnesses8.map (NumericArithmeticChecks.combine babyBearModulus relations) = combinations8
numeric_data_binding combinations_binding9 : witnesses9.map (NumericArithmeticChecks.combine babyBearModulus relations) = combinations9
numeric_data_binding combinations_binding10 : witnesses10.map (NumericArithmeticChecks.combine babyBearModulus relations) = combinations10
numeric_data_binding combinations_binding11 : witnesses11.map (NumericArithmeticChecks.combine babyBearModulus relations) = combinations11
numeric_data_binding combinations_binding12 : witnesses12.map (NumericArithmeticChecks.combine babyBearModulus relations) = combinations12
numeric_data_binding combinations_binding13 : witnesses13.map (NumericArithmeticChecks.combine babyBearModulus relations) = combinations13
theorem combinations_binding : CleanIdealChecks.mapTable (NumericArithmeticChecks.combine babyBearModulus relations) witnesses = combinations :=
  (congrArg₂ (NumericPolynomialChecks.LookupTable.branch 112) (congrArg₂ (NumericPolynomialChecks.LookupTable.branch 48) (congrArg₂ (NumericPolynomialChecks.LookupTable.branch 16) (congrArg NumericPolynomialChecks.LookupTable.leaf combinations_binding0) (congrArg₂ (NumericPolynomialChecks.LookupTable.branch 16) (congrArg NumericPolynomialChecks.LookupTable.leaf combinations_binding1) (congrArg NumericPolynomialChecks.LookupTable.leaf combinations_binding2))) (congrArg₂ (NumericPolynomialChecks.LookupTable.branch 32) (congrArg₂ (NumericPolynomialChecks.LookupTable.branch 16) (congrArg NumericPolynomialChecks.LookupTable.leaf combinations_binding3) (congrArg NumericPolynomialChecks.LookupTable.leaf combinations_binding4)) (congrArg₂ (NumericPolynomialChecks.LookupTable.branch 16) (congrArg NumericPolynomialChecks.LookupTable.leaf combinations_binding5) (congrArg NumericPolynomialChecks.LookupTable.leaf combinations_binding6)))) (congrArg₂ (NumericPolynomialChecks.LookupTable.branch 48) (congrArg₂ (NumericPolynomialChecks.LookupTable.branch 16) (congrArg NumericPolynomialChecks.LookupTable.leaf combinations_binding7) (congrArg₂ (NumericPolynomialChecks.LookupTable.branch 16) (congrArg NumericPolynomialChecks.LookupTable.leaf combinations_binding8) (congrArg NumericPolynomialChecks.LookupTable.leaf combinations_binding9))) (congrArg₂ (NumericPolynomialChecks.LookupTable.branch 32) (congrArg₂ (NumericPolynomialChecks.LookupTable.branch 16) (congrArg NumericPolynomialChecks.LookupTable.leaf combinations_binding10) (congrArg NumericPolynomialChecks.LookupTable.leaf combinations_binding11)) (congrArg₂ (NumericPolynomialChecks.LookupTable.branch 16) (congrArg NumericPolynomialChecks.LookupTable.leaf combinations_binding12) (congrArg NumericPolynomialChecks.LookupTable.leaf combinations_binding13)))))


theorem sources : CleanIdealRows.Bindings babyBearModulus rowCapture := ⟨expanded_binding, combinations_binding⟩
end Airbender.Compiler.CleanIdealNative.BlakeRoundCached
