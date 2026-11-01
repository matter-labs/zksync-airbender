"""Generate untrusted packed normalization traces and dense capture adapters."""
import json

DENSE_FAMILIES = {"bigint", "keccak"}
PRIME = 2013265921
WORD = 1 << 64
COEFFICIENT = 1 << 32

DATA_TEMPLATE = '''open NumericPolynomialChecks

numeric_polynomials numericSource from "PATH" ["source"]
numeric_polynomials numericLowered from "PATH" ["lowered"]
numeric_polynomials numericExtensionData from "PATH" ["extension"]
numeric_combinations numericBackward from "PATH" ["backward"]
numeric_combinations numericForward from "PATH" ["forward"]
numeric_naturals numericKeys from "PATH" ["keys"]

numeric_data_binding numericLowered_binding :
  native.artifact.translation.lowered.map encode = numericLowered
numeric_data_binding numericExtensionData_binding :
  native.extensionData.toList.map encode = numericExtensionData
numeric_data_binding numericBackward_binding :
  native.backwardData.toList.map encodeCombination = numericBackward
numeric_data_binding numericForward_binding :
  native.forwardData.toList.map encodeCombination = numericForward
numeric_polynomials numericSourceHelpers from "PATH" ["sourceHelpers"]
numeric_expressions numericSourceExpressions from "PATH" ["sourceExpressions"]
def originalSourceExpressions : List (Expression INPUTS Source.BaseField) := [EXPRESSIONS]

numeric_data_binding sourceExpressionLayout : native.artifact.source =
  originalSourceExpressions.map Expression.polynomial ++
    native.helperAssertions.map (Source.HelperAssertion.polynomial native.helperPlacement)
numeric_data_binding numericSourceExpressions_binding :
  originalSourceExpressions.map NumericExpressionChecks.encode = numericSourceExpressions
numeric_data_binding numericSourceHelpers_binding :
  (native.helperAssertions.map (Source.HelperAssertion.polynomial native.helperPlacement)).map encode = numericSourceHelpers
numeric_data_binding numericSourceExpansion_binding :
  numericSourceExpressions.map (NumericExpressionChecks.Code.polynomial babyBearModulus) ++ numericSourceHelpers = numericSource
theorem numericSource_binding : native.artifact.source.map encode = numericSource :=
  (congrArg (List.map encode) sourceExpressionLayout).trans
    (NumericExpressionChecks.source_binding originalSourceExpressions
      (native.helperAssertions.map (Source.HelperAssertion.polynomial native.helperPlacement))
      numericSourceExpressions numericSourceHelpers numericSource
      numericSourceExpressions_binding numericSourceHelpers_binding numericSourceExpansion_binding)

numeric_polynomials numericNormalizedSource from "PATH" ["sourceNormalized"]
numeric_data_binding fastNormalizedSource :
  numericSource.map (FastNormalization.normalize babyBearModulus) = numericNormalizedSource
theorem numericNormalizedSource_binding : numericSource.map (NumericPolynomialChecks.normalize babyBearModulus) = numericNormalizedSource :=
  (FastNormalization.map_eq babyBearModulus numericSource).symm.trans fastNormalizedSource
numeric_polynomials numericRawGateInputs from "PATH" ["gateInput"]
numeric_data_binding numericRawGateInputs_binding : native.artifact.gates.map (fun gate => encode (NumericArithmeticChecks.gateInput gate)) = numericRawGateInputs

numeric_polynomials numericGateInputs from "PATH" ["gateInputNormalized"]
numeric_data_binding fastGateInputs : numericRawGateInputs.map (FastNormalization.normalize babyBearModulus) = numericGateInputs
theorem numericRawGateInputs_normalization : numericRawGateInputs.map (NumericPolynomialChecks.normalize babyBearModulus) = numericGateInputs :=
  (FastNormalization.map_eq babyBearModulus numericRawGateInputs).symm.trans fastGateInputs
numeric_polynomials numericRawGateOutputs from "PATH" ["gateOutput"]
numeric_data_binding numericRawGateOutputs_binding : native.artifact.gates.map (fun gate => encode (NumericArithmeticChecks.gateOutput gate)) = numericRawGateOutputs

numeric_polynomials numericGateOutputs from "PATH" ["gateOutputNormalized"]
numeric_data_binding fastGateOutputs : numericRawGateOutputs.map (FastNormalization.normalize babyBearModulus) = numericGateOutputs
theorem numericRawGateOutputs_normalization : numericRawGateOutputs.map (NumericPolynomialChecks.normalize babyBearModulus) = numericGateOutputs :=
  (FastNormalization.map_eq babyBearModulus numericRawGateOutputs).symm.trans fastGateOutputs


'''

BINDING_TEMPLATE = '''open NumericPolynomialChecks
local instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem numericGateInputs_binding :
  native.artifact.gates.map (fun gate => NumericPolynomialChecks.normalize babyBearModulus
    (encode (NumericArithmeticChecks.gateInput gate))) = numericGateInputs :=
  (List.map_map (g := NumericPolynomialChecks.normalize babyBearModulus)
    (f := fun gate => encode (NumericArithmeticChecks.gateInput gate)) (l := native.artifact.gates)).symm.trans
    ((congrArg (List.map (NumericPolynomialChecks.normalize babyBearModulus)) numericRawGateInputs_binding).trans numericRawGateInputs_normalization)
theorem numericGateOutputs_binding :
  native.artifact.gates.map (fun gate => NumericPolynomialChecks.normalize babyBearModulus
    (encode (NumericArithmeticChecks.gateOutput gate))) = numericGateOutputs :=
  (List.map_map (g := NumericPolynomialChecks.normalize babyBearModulus)
    (f := fun gate => encode (NumericArithmeticChecks.gateOutput gate)) (l := native.artifact.gates)).symm.trans
    ((congrArg (List.map (NumericPolynomialChecks.normalize babyBearModulus)) numericRawGateOutputs_binding).trans numericRawGateOutputs_normalization)
numeric_data_binding numericKeys_binding :
  (native.addresses.map AddressUniqueChecks.addressCode).insertionSort (fun a b => a ≤ b) = numericKeys

noncomputable def numericCapture : NumericArithmeticChecks.Capture INPUTS := {
  sourceRows := numericSource.tree
  normalizedSourceRows := numericNormalizedSource.tree
  lowerRows := numericLowered.tree
  computedRows := numericExtensionData.tree
  backwardRows := numericBackward.tree
  forwardRows := numericForward.tree
  gateInputs := numericGateInputs.tree
  gateOutputs := numericGateOutputs.tree
  sortedAddressKeys := numericKeys
}

theorem numericBindings : NumericArithmeticChecks.Bindings native.addresses native.artifact native.certificate numericCapture := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, numericKeys_binding⟩
  · exact numericSource_binding.trans numericSource.tree_binding.symm
  · exact (List.map_map (g := NumericPolynomialChecks.normalize babyBearModulus) (f := encode) (l := native.artifact.source)).symm.trans
      ((congrArg (List.map (NumericPolynomialChecks.normalize babyBearModulus)) numericSource_binding).trans
        (numericNormalizedSource_binding.trans numericNormalizedSource.tree_binding.symm))
  · exact numericLowered_binding.trans numericLowered.tree_binding.symm
  · intro wire; rfl
  · intro wire
    exact NumericArithmeticChecks.initial_extension (by decide) native.extensionData _
      numericExtensionData.tree_valid
      (numericExtensionData_binding.trans numericExtensionData.tree_binding.symm) wire
  · intro index
    exact (NumericArithmeticChecks.vector_getD native.backwardData encodeCombination _
      numericBackward.tree_valid
      (numericBackward_binding.trans numericBackward.tree_binding.symm) index []).symm
  · intro index
    exact (NumericArithmeticChecks.vector_getD native.forwardData encodeCombination _
      numericForward.tree_valid
      (numericForward_binding.trans numericForward.tree_binding.symm) index []).symm
  · exact (NumericArithmeticChecks.map_encode_normalize native.artifact.gates NumericArithmeticChecks.gateInput).trans
      (numericGateInputs_binding.trans numericGateInputs.tree_binding.symm)
  · exact (NumericArithmeticChecks.map_encode_normalize native.artifact.gates NumericArithmeticChecks.gateOutput).trans
      (numericGateOutputs_binding.trans numericGateOutputs.tree_binding.symm)


'''

def normalize(polynomial):
    terms = {}
    for coefficient, monomial in polynomial:
        key = tuple(sorted(monomial))
        terms[key] = (terms.get(key, 0) + coefficient) % PRIME
    return [[coefficient, list(key)] for key, coefficient in sorted(terms.items()) if coefficient]


def multiply(left, right):
    return [[a * b % PRIME, x + y] for a, x in left for b, y in right]


def combination(relations, terms):
    return [term for factor, index in terms for term in multiply(factor, relations[index])]


def substitute(polynomial, inputs, extension):
    result = []
    for coefficient, monomial in polynomial:
        product = [[1, []]]
        for wire in reversed(monomial):
            product = multiply([[1, [wire]]] if wire < inputs else extension[wire - inputs], product)
        result.extend(multiply([[coefficient, []]], product))
    return result


def pack(polynomial):
    value = 0
    for coefficient, monomial in reversed(polynomial):
        monomial = sorted(monomial)
        if not monomial:
            key = 0
        elif len(monomial) == 1:
            key = 1 + 512 * monomial[0]
        elif len(monomial) == 2 and monomial[1] < 511:
            key = 2 + 512 * monomial[0] + monomial[1]
        else:
            raise ValueError("polynomial exceeds the packed monomial bounds")
        if not (0 <= coefficient < COEFFICIENT and 0 <= key < COEFFICIENT):
            raise ValueError("polynomial exceeds the packed word bounds")
        value = coefficient + COEFFICIENT * key + WORD * value
    return [len(polynomial), value]


def trace_row(expected, polynomial):
    states = [[0, pack([])]]
    terms = []
    for coefficient, monomial in reversed(polynomial):
        key = tuple(sorted(monomial))
        index = next((index for index, (_, existing) in enumerate(terms)
                      if tuple(existing) >= key), len(terms))
        terms = normalize([[coefficient, monomial]] + terms)
        states.append([index, pack(terms)])
    return {"expected": pack(expected), "input": pack(polynomial), "trace": list(reversed(states))}


def normalization_traces(payload, inputs):
    backward = [trace_row(expected, combination(payload["lowered"], terms))
                for expected, terms in zip(payload["sourceNormalized"], payload["backward"], strict=True)]
    forward = [trace_row(normalize(combination(payload["source"], terms)),
                         substitute(lowered, inputs, payload["extension"]))
               for lowered, terms in zip(payload["lowered"], payload["forward"], strict=True)]
    return backward + forward


def modules(name, case, result, foundation, wrap, expression_count):
    prefix = foundation.removesuffix("Foundation")
    path = f"artifacts/compiler/numeric-arithmetic/{name}.json"
    expressions = ", ".join(f"native.originalExpression{index}" for index in range(expression_count))
    data = DATA_TEMPLATE.replace("PATH", path).replace("INPUTS", str(len(result["inputs"]))).replace("EXPRESSIONS", expressions)
    bindings = BINDING_TEMPLATE.replace("INPUTS", str(len(result["inputs"])))
    traces = f'packed_normalization_rows numericTraceRows from "{path}" ["normalizationTraces"]'
    certificate = '''local instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

noncomputable def numericTraceCapture : NumericArithmeticTrace.Capture INPUTS := ⟨numericCapture, numericTraceRows⟩

theorem numericTraceBindings : NumericArithmeticTrace.bindingCheck
    (NumericArithmeticTrace.pairs babyBearModulus numericCapture) numericTraceRows = true := by decide +kernel

theorem numericTraceChecked : NumericArithmeticTrace.check babyBearModulus numericTraceCapture = true := by decide +kernel

theorem numericChecked : NumericArithmeticChecks.check babyBearModulus numericCapture = true :=
  NumericArithmeticTrace.check_sound babyBearModulus numericTraceCapture numericTraceBindings numericTraceChecked

theorem numericFullChecked : FullArithmeticChecks.check native.addresses native.artifact native.certificate = true :=
  NumericArithmeticChecks.full_check _ _ _ _ numericBindings numericChecked'''.replace("INPUTS", str(len(result["inputs"])))
    return [(prefix + "NumericData", wrap([foundation,
                "Airbender.Import.GKRProtocol.NumericExpressionDataImport",
                "Airbender.Proofs.GKRProtocol.FastNumericNormalization"], data)),
            (prefix + "NumericBindings", wrap([prefix + "NumericData"], bindings)),
            (prefix + "NumericTraces", wrap(["Airbender.Import.GKRProtocol.NumericTraceDataImport"], traces)),
            (prefix + "NumericCertificate", wrap([prefix + "NumericBindings", prefix + "NumericTraces",
                "Airbender.Proofs.GKRProtocol.ArithmeticNormalizationTrace"], certificate))]


def extra_roots(case, payload):
    base = "Airbender.Compiler.FullArithmeticNative." + case + "."
    names = ["originalSourceExpressions", "sourceExpressionLayout", "numericSourceExpressions",
             "numericSourceExpressions_binding", "numericSourceHelpers", "numericSourceHelpers_binding",
             "numericSourceExpansion_binding", "fastNormalizedSource", "numericRawGateInputs",
             "numericRawGateInputs_binding", "fastGateInputs", "numericRawGateInputs_normalization",
             "numericRawGateOutputs", "numericRawGateOutputs_binding", "fastGateOutputs",
             "numericRawGateOutputs_normalization", "numericTraceRows", "numericTraceCapture",
             "numericTraceBindings", "numericTraceChecked"]
    for field, name in [("sourceHelpers", "numericSourceHelpers"), ("gateInput", "numericRawGateInputs"),
                        ("gateOutput", "numericRawGateOutputs")]:
        names += [name + "." + suffix for suffix in ["tree", "tree_binding", "tree_valid"]]
        names += [name + ".leaf" + str(index) for index in range(max(1, (len(payload[field]) + 15) // 16))]
    names += ["numericTraceRows.leaf" + str(index)
              for index in range(max(1, (len(payload["normalizationTraces"]) + 7) // 8))]
    return [base + name for name in names]
