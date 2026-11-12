module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.CleanIdealNative.BigintCachedData
public import Proven.GKRProtocol.CleanIdealNative.BigintCachedTraces
public import Proven.GKRProtocol.CleanIdealTrace
public import Proven.Import.GKRProtocol.NumericArithmeticDataImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.CleanIdealNative.BigintCached
set_option maxRecDepth 32768

def traceCapture : CleanIdealTrace.Capture := ⟨capture, normalized, expanded, combinations, traceRows⟩
numeric_data_binding expanded_binding0 : codes0.map (NumericExpressionChecks.Code.polynomial babyBearModulus) = expanded0
numeric_data_binding expanded_binding1 : codes1.map (NumericExpressionChecks.Code.polynomial babyBearModulus) = expanded1
numeric_data_binding expanded_binding2 : codes2.map (NumericExpressionChecks.Code.polynomial babyBearModulus) = expanded2
numeric_data_binding expanded_binding3 : codes3.map (NumericExpressionChecks.Code.polynomial babyBearModulus) = expanded3
numeric_data_binding expanded_binding4 : codes4.map (NumericExpressionChecks.Code.polynomial babyBearModulus) = expanded4
numeric_data_binding expanded_binding5 : codes5.map (NumericExpressionChecks.Code.polynomial babyBearModulus) = expanded5
numeric_data_binding expanded_binding6 : codes6.map (NumericExpressionChecks.Code.polynomial babyBearModulus) = expanded6
numeric_data_binding expanded_binding7 : codes7.map (NumericExpressionChecks.Code.polynomial babyBearModulus) = expanded7
numeric_data_binding expanded_binding8 : codes8.map (NumericExpressionChecks.Code.polynomial babyBearModulus) = expanded8
theorem expanded_binding : CleanIdealChecks.mapTable (NumericExpressionChecks.Code.polynomial babyBearModulus) codes = expanded :=
  (congrArg₂ (NumericPolynomialChecks.LookupTable.branch 64) (congrArg₂ (NumericPolynomialChecks.LookupTable.branch 32) (congrArg₂ (NumericPolynomialChecks.LookupTable.branch 16) (congrArg NumericPolynomialChecks.LookupTable.leaf expanded_binding0) (congrArg NumericPolynomialChecks.LookupTable.leaf expanded_binding1)) (congrArg₂ (NumericPolynomialChecks.LookupTable.branch 16) (congrArg NumericPolynomialChecks.LookupTable.leaf expanded_binding2) (congrArg NumericPolynomialChecks.LookupTable.leaf expanded_binding3))) (congrArg₂ (NumericPolynomialChecks.LookupTable.branch 32) (congrArg₂ (NumericPolynomialChecks.LookupTable.branch 16) (congrArg NumericPolynomialChecks.LookupTable.leaf expanded_binding4) (congrArg NumericPolynomialChecks.LookupTable.leaf expanded_binding5)) (congrArg₂ (NumericPolynomialChecks.LookupTable.branch 16) (congrArg NumericPolynomialChecks.LookupTable.leaf expanded_binding6) (congrArg₂ (NumericPolynomialChecks.LookupTable.branch 16) (congrArg NumericPolynomialChecks.LookupTable.leaf expanded_binding7) (congrArg NumericPolynomialChecks.LookupTable.leaf expanded_binding8)))))

numeric_data_binding combinations_binding0 : witnesses0.map (NumericArithmeticChecks.combine babyBearModulus relations) = combinations0
numeric_data_binding combinations_binding1 : witnesses1.map (NumericArithmeticChecks.combine babyBearModulus relations) = combinations1
numeric_data_binding combinations_binding2 : witnesses2.map (NumericArithmeticChecks.combine babyBearModulus relations) = combinations2
numeric_data_binding combinations_binding3 : witnesses3.map (NumericArithmeticChecks.combine babyBearModulus relations) = combinations3
numeric_data_binding combinations_binding4 : witnesses4.map (NumericArithmeticChecks.combine babyBearModulus relations) = combinations4
numeric_data_binding combinations_binding5 : witnesses5.map (NumericArithmeticChecks.combine babyBearModulus relations) = combinations5
numeric_data_binding combinations_binding6 : witnesses6.map (NumericArithmeticChecks.combine babyBearModulus relations) = combinations6
numeric_data_binding combinations_binding7 : witnesses7.map (NumericArithmeticChecks.combine babyBearModulus relations) = combinations7
numeric_data_binding combinations_binding8 : witnesses8.map (NumericArithmeticChecks.combine babyBearModulus relations) = combinations8
theorem combinations_binding : CleanIdealChecks.mapTable (NumericArithmeticChecks.combine babyBearModulus relations) witnesses = combinations :=
  (congrArg₂ (NumericPolynomialChecks.LookupTable.branch 64) (congrArg₂ (NumericPolynomialChecks.LookupTable.branch 32) (congrArg₂ (NumericPolynomialChecks.LookupTable.branch 16) (congrArg NumericPolynomialChecks.LookupTable.leaf combinations_binding0) (congrArg NumericPolynomialChecks.LookupTable.leaf combinations_binding1)) (congrArg₂ (NumericPolynomialChecks.LookupTable.branch 16) (congrArg NumericPolynomialChecks.LookupTable.leaf combinations_binding2) (congrArg NumericPolynomialChecks.LookupTable.leaf combinations_binding3))) (congrArg₂ (NumericPolynomialChecks.LookupTable.branch 32) (congrArg₂ (NumericPolynomialChecks.LookupTable.branch 16) (congrArg NumericPolynomialChecks.LookupTable.leaf combinations_binding4) (congrArg NumericPolynomialChecks.LookupTable.leaf combinations_binding5)) (congrArg₂ (NumericPolynomialChecks.LookupTable.branch 16) (congrArg NumericPolynomialChecks.LookupTable.leaf combinations_binding6) (congrArg₂ (NumericPolynomialChecks.LookupTable.branch 16) (congrArg NumericPolynomialChecks.LookupTable.leaf combinations_binding7) (congrArg NumericPolynomialChecks.LookupTable.leaf combinations_binding8)))))



theorem sources : CleanIdealTrace.Bindings babyBearModulus traceCapture := ⟨expanded_binding, combinations_binding⟩

end Airbender.Compiler.CleanIdealNative.BigintCached
