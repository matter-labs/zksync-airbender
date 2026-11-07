#!/usr/bin/env python3
"""Emit untrusted numeric arithmetic payloads and complete capture modules."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

import gkr_dense_arithmetic as dense

from export_gkr_translations import FAMILIES, LEAN
from gkr_wiring_instances import CASES

NUMERIC_CAPTURES = {stem + mode for stem in CASES if stem != "AddSub"
                    for mode in ("Cached",)}
PRIME = 2013265921


def normalize(polynomial):
    terms = {}
    for coefficient, monomial in polynomial:
        key = tuple(sorted(monomial))
        terms[key] = (terms.get(key, 0) + coefficient) % PRIME
    return [[coefficient, list(key)] for key, coefficient in sorted(terms.items()) if coefficient]


def provenance(root, name, selectors):
    paths = [f"artifacts/compiler/{name}.json", f"artifacts/compiler/{name}-source.json",
             "Airbender/Import/GKRProtocol/FullArithmeticImport.lean"]
    hashes = {path: hashlib.sha256((root / path).read_bytes()).hexdigest() for path in paths}
    hashes["selectors"] = hashlib.sha256(json.dumps(selectors, separators=(",", ":")).encode()).hexdigest()
    return hashes


def is_dense(name):
    return any(name.startswith(family + "-") for family in dense.DENSE_FAMILIES)


def expression_count(root, name):
    source = json.loads((root / f"artifacts/compiler/{name}.json").read_text())["source"]
    return len(source["statements"]) + len(source["booleans"])


def prepare_payload(root, name, selectors, raw):
    payload = dict(raw)
    payload["sourceNormalized"] = [normalize(row) for row in raw["source"]]
    if is_dense(name):
        count = expression_count(root, name)
        if len(raw.get("sourceExpressions", [])) != count:
            raise ValueError(f"source expression count changed: {name}")
        payload["sourceHelpers"] = raw["source"][count:]
    for side in ("gateInput", "gateOutput"):
        payload[side + "Normalized"] = [normalize(row) for row in raw[side]]
        if not is_dense(name):
            payload.pop(side)
    payload["keys"] = sorted(payload["keys"])
    if is_dense(name):
        payload["normalizationTraces"] = dense.normalization_traces(payload, len(selectors["inputs"]))
    payload["provenance"] = provenance(root, name, selectors)
    return payload


def payload_path(root, name):
    return root / f"artifacts/compiler/numeric-arithmetic/{name}.json"


def check_payload(root, name, selectors):
    payload = json.loads(payload_path(root, name).read_text())
    if payload.get("provenance") != provenance(root, name, selectors):
        raise ValueError(f"numeric arithmetic provenance changed: {name}")
    expected = {"source": selectors["counts"]["source_obligations"],
                "sourceNormalized": selectors["counts"]["source_obligations"],
                "lowered": selectors["counts"]["relations"],
                "extension": len(selectors["addresses"]) - len(selectors["inputs"]),
                "backward": selectors["counts"]["source_obligations"],
                "forward": selectors["counts"]["relations"],
                "gateInputNormalized": selectors["counts"]["relations"],
                "gateOutputNormalized": selectors["counts"]["relations"],
                "keys": len(selectors["addresses"])}
    if is_dense(name):
        expected.update({"sourceExpressions": expression_count(root, name),
                         "sourceHelpers": expected["source"] - expression_count(root, name),
                         "gateInput": expected["lowered"], "gateOutput": expected["lowered"],
                         "normalizationTraces": expected["source"] + expected["lowered"]})
    if set(payload) != {*expected, "provenance"}:
        raise ValueError(f"numeric arithmetic field set changed: {name}")
    for field, count in expected.items():
        if len(payload[field]) != count:
            raise ValueError(f"numeric arithmetic row count changed: {name}/{field}")
    if payload["keys"] != sorted(payload["keys"]):
        raise ValueError(f"numeric arithmetic keys are not sorted: {name}")
    if is_dense(name) and payload["normalizationTraces"] != dense.normalization_traces(payload, len(selectors["inputs"])):
        raise ValueError(f"packed normalization trace changed: {name}")
    return payload


def modules(name, case, result, foundation, wrap):
    if is_dense(name):
        return dense.modules(name, case, result, foundation, wrap, expression_count(LEAN, name))
    prefix = foundation.removesuffix("Foundation")
    path = f"artifacts/compiler/numeric-arithmetic/{name}.json"
    data = "open NumericPolynomialChecks\n\n"
    for field, declaration in [("source", "numericSource"), ("sourceNormalized", "numericNormalizedSource"),
                               ("lowered", "numericLowered"),
                               ("extension", "numericExtensionData"),
                               ("gateInputNormalized", "numericGateInputs"),
                               ("gateOutputNormalized", "numericGateOutputs")]:
        data += f'numeric_polynomials {declaration} from "{path}" ["{field}"]\n'
    for field in ("backward", "forward"):
        data += f'numeric_combinations numeric{field.title()} from "{path}" ["{field}"]\n'
    data += f'numeric_naturals numericKeys from "{path}" ["keys"]\n\n'
    for declaration, expression in [
            ("numericSource", "native.artifact.source.map encode"),
            ("numericNormalizedSource", "numericSource.map (NumericPolynomialChecks.normalize babyBearModulus)"),
            ("numericLowered", "native.artifact.translation.lowered.map encode"),
            ("numericExtensionData", "native.extensionData.toList.map encode"),
            ("numericBackward", "native.backwardData.toList.map encodeCombination"),
            ("numericForward", "native.forwardData.toList.map encodeCombination")]:
        data += f"numeric_data_binding {declaration}_binding :\n  {expression} = {declaration}\n"
    bindings = '''open NumericPolynomialChecks
local instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

numeric_data_binding numericGateInputs_binding :
  native.artifact.gates.map (fun gate => NumericPolynomialChecks.normalize babyBearModulus
    (encode (NumericArithmeticChecks.gateInput gate))) = numericGateInputs
numeric_data_binding numericGateOutputs_binding :
  native.artifact.gates.map (fun gate => NumericPolynomialChecks.normalize babyBearModulus
    (encode (NumericArithmeticChecks.gateOutput gate))) = numericGateOutputs
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
'''.replace("INPUTS", str(len(result["inputs"])))
    certificate = '''local instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem numericChecked : NumericArithmeticChecks.check babyBearModulus numericCapture = true := by decide +kernel

theorem numericFullChecked : FullArithmeticChecks.check native.addresses native.artifact native.certificate = true :=
  NumericArithmeticChecks.full_check _ _ _ _ numericBindings numericChecked'''
    return [(prefix + "NumericData", wrap([foundation, "Airbender.Import.GKRProtocol.NumericArithmeticDataImport"], data)),
            (prefix + "NumericBindings", wrap([prefix + "NumericData"], bindings)),
            (prefix + "NumericCertificate", wrap([prefix + "NumericBindings"], certificate))]


def capture_roots(case, payload):
    """Audit every numeric payload, structural binding and complete result."""
    base = "Airbender.Compiler.FullArithmeticNative." + case + "."
    fields = [("source", "numericSource"), ("sourceNormalized", "numericNormalizedSource"),
              ("lowered", "numericLowered"), ("extension", "numericExtensionData"),
              ("gateInputNormalized", "numericGateInputs"), ("gateOutputNormalized", "numericGateOutputs"),
              ("backward", "numericBackward"), ("forward", "numericForward")]
    declarations = [name for _, name in fields] + ["numericKeys"]
    roots = [base + name for name in declarations]
    roots += [base + name + "_binding" for name in declarations]
    roots += [base + name for name in ["numericCapture", "numericBindings", "numericChecked",
                                      "numericFullChecked", "native.captureChecked"]]
    for field, name in fields:
        roots += [base + name + "." + suffix for suffix in ["tree", "tree_binding", "tree_valid"]]
        roots += [base + name + ".leaf" + str(index)
                  for index in range(max(1, (len(payload[field]) + 15) // 16))]
    if "normalizationTraces" in payload:
        roots += dense.extra_roots(case, payload)
    return roots


def main():
    from gkr_full_arithmetic_certificate import synthesize
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--family", choices=[family for family, stem in zip(FAMILIES, CASES, strict=True)
                                               if stem + "Cached" in NUMERIC_CAPTURES], action="append")
    parser.add_argument("--mode", choices=("cached",), action="append")
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--raw-dir", type=Path)
    args = parser.parse_args()
    for family, stem in zip(FAMILIES, CASES, strict=True):
        if stem + "Cached" not in NUMERIC_CAPTURES or (args.family and family not in args.family):
            continue
        for mode in ("cached",):
            if args.mode and mode not in args.mode:
                continue
            name = family + "-" + mode
            case = stem + mode.title()
            root = LEAN / "artifacts/compiler"
            selectors = synthesize(json.loads((root / (name + ".json")).read_text()),
                                   json.loads((root / (name + "-source.json")).read_text()))
            if args.write:
                with tempfile.TemporaryDirectory(prefix="airbender-numeric-export-") as directory:
                    raw = (args.raw_dir / (case + "-numeric-export.json") if args.raw_dir else Path(directory) / "raw.json")
                    if not args.raw_dir:
                        source = Path(directory) / "Export.lean"
                        source.write_text(f"import Airbender.Proofs.GKRProtocol.FullArithmeticNative.{case}Foundation\n" +
                                          (LEAN / "scripts/ExportNumericArithmetic.lean").read_text() +
                                          "\n-- Reflection runs only in this untrusted export command.\n" +
                                          "set_option maxRecDepth 32768\nset_option maxHeartbeats 4000000\n" +
                                          f'export_numeric_arithmetic Airbender.Compiler.FullArithmeticNative.{case}.native to "{raw}"\n')
                        if is_dense(name):
                            expressions = Path(directory) / "expressions.json"
                            with source.open("a") as output:
                                output.write(f'export_source_expressions Airbender.Compiler.FullArithmeticNative.{case}.native count {expression_count(LEAN, name)} to "{expressions}"\n')
                        subprocess.run(["lake", "env", "lean", "--tstack=2097152", str(source)], cwd=LEAN, check=True)
                    raw_payload = json.loads(raw.read_text())
                    if is_dense(name) and not args.raw_dir:
                        raw_payload["sourceExpressions"] = json.loads(expressions.read_text())
                    payload = prepare_payload(LEAN, name, selectors, raw_payload)
                    path = payload_path(LEAN, name)
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_text(json.dumps(payload, sort_keys=True, separators=(",", ":")) + "\n")
            check_payload(LEAN, name, selectors)
            print(f"PASS numeric payload provenance and complete dimensions: {name}")


if __name__ == "__main__":
    main()
