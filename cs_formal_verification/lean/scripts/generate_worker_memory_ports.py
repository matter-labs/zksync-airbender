#!/usr/bin/env python3
"""Emit the RAM-product instance, the RAM output proof and the memory witness of each cached worker capture.

The compiled circuit gives the RAM outputs, the execute mask and its copy chain. The kernel checks every
emitted fact against the imported capture. The program check and the witness have separate modules, so each
module stays in the per-module time budget. `--check` fails when a committed module differs from the output."""
from pathlib import Path
import argparse
import json
import sys

ROOT = Path(__file__).resolve().parents[1]
GKR = ROOT / "proven/Proven/GKRProtocol"

# name, compiler capture, compiled layout, artifact namespace, request CSR, row kind, row constructor and
# the stem of the arithmetic witness theorem
WORKERS = [
    ("Bigint", "bigint-cached", "bigint_with_extended_control", "Airbender.Bigint", 0x7CA,
     "standard", ".bigint", "bigint"),
    ("BlakeG", "blake-g-cached", "blake2_g_function", "Airbender.Blake2G", 0x7C8,
     "standard", ".blakeG", "blakeG"),
    ("BlakeRound", "blake-round-cached", "blake2_with_extended_control", "Airbender.Blake2Round", 0x7C7,
     "standard", ".blakeRound", "blakeRound"),
    ("KeccakColumnParity", "keccak-column-parity-cached", "keccak_column_parity",
     "Airbender.Keccak.Split.ColumnParity", 0x7CD, "split", ".columnParity", "keccakColumnParity"),
    ("KeccakThetaRho", "keccak-theta-rho-cached", "keccak_theta_rho",
     "Airbender.Keccak.Split.ThetaRho", 0x7CC, "split", ".thetaRho", "keccakThetaRho"),
]


def address(value):
    """Lean syntax of one compiled GKR address."""
    if "InnerLayer" in value:
        return f".InnerLayer {value['InnerLayer']['layer']} {value['InnerLayer']['offset']}"
    if "BaseLayerMemory" in value:
        return f".BaseLayerMemory {value['BaseLayerMemory']}"
    raise ValueError(f"unexpected address {value}")


def layout_facts(layout):
    """The RAM outputs, the execute mask, its copy-chain root and the chain length."""
    circuit = json.loads((ROOT.parent.parent / f"cs/compiled_circuits/{layout}_layout_gkr.json").read_text())
    relations = [gate["enforced_relation"] for layer in circuit["layers"]
                 for gate in layer["gates"] + layer["gates_with_external_connections"]]
    outputs = circuit["global_output_map"]["PermutationProduct"]
    masks = {json.dumps(relation["MaskIntoIdentityProduct"]["mask"]) for relation in relations
             if "MaskIntoIdentityProduct" in relation}
    if len(outputs) != 2 or len(masks) != 1:
        raise ValueError(f"{layout}: unexpected RAM output or mask shape")
    mask = json.loads(masks.pop())
    root, steps = mask, 0
    while True:
        sources = [relation["CopyInBaseField"]["input"] for relation in relations
                   if "CopyInBaseField" in relation and relation["CopyInBaseField"]["output"] == root]
        if not sources:
            break
        root, steps = sources[0], steps + 1
    if "BaseLayerMemory" not in root:
        raise ValueError(f"{layout}: the execute mask is not a copy of a memory column")
    return outputs, mask, root["BaseLayerMemory"], steps


def product_module(name, capture):
    return f"""module
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.NativeProductImport

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.ProductNative.{name}Cached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_native_products native from "artifacts/compiler/{capture}.json"

end Airbender.Compiler.ProductNative.{name}Cached
"""


def ports_module(worker):
    name, _, layout, artifact, csr, kind, constructor, _ = worker
    outputs, mask, execute, steps = layout_facts(layout)
    read, write = (address(output) for output in outputs)
    mask = address(mask)
    product = f"ProductNative.{name}Cached.native"
    ports = f"{artifact}.importedConstraintsMemoryPorts.toList"
    columns = f"{artifact}.importedConstraintsDelegationColumns"
    row = "Delegation.Row babyBearModulus" if kind == "standard" else "Keccak.Split.Native.Row babyBearModulus"
    return f"""module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.NativeMemoryWorkers
public import Proven.GKRProtocol.ProductNative.{name}Cached
public import Proven.KernelRfl
public import Human.Compiler.WorkerMemoryPorts

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.WorkerPortsNative.{name}Cached
open Airbender Airbender.Compiler NativeMemoryBridge
set_option maxRecDepth 32768

/-- The cached capture. -/
noncomputable abbrev circuit : Circuit := Captures.{name}.imported.circuit

/-- Base-field caches and gates of the capture write its base-field wires. -/
noncomputable abbrev roles : GKRAddress → Bool := structuralRoles circuit

/-- The imported product gates are the RAM-product recipes of the imported capture. -/
theorem gates_binding : {product}.gates = productGates circuit := by
  kernel_rfl

/-- Every recipe reads its operands with the structural field roles. -/
theorem typed : typingChecked roles circuit = true := by
  decide +kernel

/-- The RAM output map of the capture. -/
theorem outputs : NativeMemory.ramOutputs circuit = [{read}, {write}] := by
  kernel_rfl

/-- Both RAM outputs are extension wires. -/
theorem outputRoles : isBase roles ({read}) = false ∧ isBase roles ({write}) = false := by
  decide +kernel

/-- The execute mask is a base wire. -/
theorem maskRole : isBase roles ({mask}) = true := by
  decide +kernel

/-- The copy chain of the execute mask starts at a memory column. -/
theorem maskRoot : copyRoot circuit {steps} ({mask}) = .BaseLayerMemory {execute} := by
  decide +kernel

/-- That memory column is the execute column of the placement. -/
theorem execute : memoryVariable circuit {execute} = some {columns}.execute := by
  decide +kernel

/-- The read tree reads the port read tuples and the issued request tuple. -/
theorem reads : tuplesMatch circuit {product}.registry {product}.memoryReadProduct.leaves
    (modelReadTuples {ports} 0x{csr:X} {columns}.invocation) = true := by
  decide +kernel

/-- The write tree reads the port write tuples and the returned request tuple. -/
theorem writes : tuplesMatch circuit {product}.registry {product}.memoryWriteProduct.leaves
    (modelWriteTuples {ports} 0x{csr:X} {columns}.invocation) = true := by
  decide +kernel

/-- Native base gates, extension caches and product gates give the RAM outputs from the model tokens. -/
theorem ram_products {{R : Type}} [CommRing R] (challenges : NativeMemory.Challenges R)
    (physical : GKRAddress → NativeArithmetic.F) (values : GKRAddress → R) (assignment : Nat → NativeArithmetic.F)
    (accepted : NativeArithmetic.Holds circuit physical)
    (placement : NativeArithmetic.PlacementAgreement circuit physical assignment)
    (extension : NativeMemory.Holds circuit challenges physical values) :
    NativeMemory.RamProducts circuit challenges values (assignment {columns}.execute)
      (NativeMemory.{kind}Reads (⟨{constructor}, assignment⟩ : {row}))
      (NativeMemory.{kind}Writes (⟨{constructor}, assignment⟩ : {row})) := by
  have holds : ∀ gate ∈ {product}.gates,
      gate.Holds challenges.memory.embed (cacheChallenges challenges) (wires challenges roles physical values) := by
    rw [gates_binding]
    exact products_hold challenges roles physical values typed extension
  exact worker_ram_products challenges roles physical values assignment typed accepted extension placement outputs
    outputRoles maskRole maskRoot execute reads writes
    ({product}.memoryReadProductReduction _ _ _ holds)
    ({product}.memoryWriteProductReduction _ _ _ holds)

end Airbender.Compiler.WorkerPortsNative.{name}Cached
"""


def program_module(worker):
    name = worker[0]
    return f"""module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.NativeMemoryProgram
public import Proven.GKRProtocol.WorkerPortsNative.{name}Cached

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.WorkerPortsNative.{name}Cached
open Airbender Airbender.Compiler NativeMemoryBridge
set_option maxRecDepth 32768

/-- The witness program reads only base and earlier wires. -/
theorem program_valid : (extensionProgram roles circuit).check (isBase roles) [] = true := by
  decide +kernel

end Airbender.Compiler.WorkerPortsNative.{name}Cached
"""


def witness_module(worker):
    name, _, _, _, _, kind, constructor, stem = worker
    witness = "Arithmetic" if kind == "standard" else "WorkerArithmetic"
    return f"""module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.WorkerPortsNative.{name}CachedProgram
public import Proven.Final.Compiler.{witness}

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.WorkerPortsNative.{name}Cached
open Airbender Airbender.Compiler NativeMemoryBridge
set_option maxRecDepth 32768

/-- The witness program covers every extension cache and gate. -/
theorem program_covered : programCovered roles circuit = true := by
  decide +kernel

/-- The program values of the arithmetic witness meet the memory premises. -/
theorem satisfiable : {name}CachedMemorySatisfiableClaim := by
  obtain ⟨physical, logical, accepted, placement⟩ := {stem}_cached_arithmetic_satisfiable
  let challenges : NativeMemory.Challenges NativeArithmetic.F := ⟨⟨RingHom.id _, 0, fun _ => 0, fun _ => 0⟩, 0⟩
  exact ⟨challenges, physical, programValues roles circuit challenges physical, ⟨{constructor}, logical⟩, rfl, accepted,
    placement, program_holds challenges roles physical program_valid program_covered typed⟩

end Airbender.Compiler.WorkerPortsNative.{name}Cached
"""


def outputs(selected):
    for worker in WORKERS:
        if selected and worker[0] not in selected:
            continue
        name, capture = worker[0], worker[1]
        yield GKR / f"ProductNative/{name}Cached.lean", product_module(name, capture)
        yield GKR / f"WorkerPortsNative/{name}Cached.lean", ports_module(worker)
        yield GKR / f"WorkerPortsNative/{name}CachedProgram.lean", program_module(worker)
        yield GKR / f"WorkerPortsNative/{name}CachedWitness.lean", witness_module(worker)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("workers", nargs="*")
    args = parser.parse_args()
    stale = []
    for path, text in outputs(set(args.workers)):
        if args.check:
            if not path.exists() or path.read_text() != text:
                stale.append(str(path.relative_to(ROOT)))
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
    if stale:
        sys.exit("FAIL stale worker memory modules: " + ", ".join(stale))
    print("PASS worker memory modules" if args.check else "wrote worker memory modules")


if __name__ == "__main__":
    main()
