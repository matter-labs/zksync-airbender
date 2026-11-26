import Human.Compiler.NativePublicSetup
import Human.Compiler.WorkerLookups
import Human.ISA.Sail.Theorems
import Proven.KernelRfl

/-! Spot checks of the imported data. Each example reads one value of an imported cached circuit, or decodes one
    program word with Sail and finds its native query in the decoder table. The comment above each example names
    the JSON file and the JSON path of the value. Coefficients are the raw Montgomery values of the file. -/

set_option warningAsError true
set_option maxRecDepth 32768

open Sail SailRV32 SailRV32.Functions Human

namespace Airbender.Tests.ImportSpotChecks
open Compiler Trace

/-- The raw coefficient and address of linear term `term` of quadratic gate `gate` in layer `layer`. -/
def linearTerm (circuit : Circuit) (layer gate term : Nat) : Option (Nat × GKRAddress) := do
  let artifact ← (← circuit.layers[layer]?).gates[gate]?
  match artifact.enforced_relation with
  | .EnforceSingleMaxQuadraticConstraint input _ | .MaxQuadratic input _ _ =>
      let (coefficient, address) ← input.linear_terms[term]?
      pure (coefficient.raw.val, address)
  | _ => none

/-- The left address, raw coefficient and right address of quadratic term `term`, factor `factor`, of gate `gate`. -/
def quadraticTerm (circuit : Circuit) (layer gate term factor : Nat) : Option (GKRAddress × Nat × GKRAddress) := do
  let artifact ← (← circuit.layers[layer]?).gates[gate]?
  match artifact.enforced_relation with
  | .EnforceSingleMaxQuadraticConstraint input _ | .MaxQuadratic input _ _ =>
      let (left, factors) ← input.quadratic_terms[term]?
      let (coefficient, right) ← factors[factor]?
      pure (left, coefficient.raw.val, right)
  | _ => none

/-- The physical address of a logical placement key. -/
def placement (circuit : Circuit) (key : Nat) : Option GKRAddress :=
  (circuit.placement_data.entries.toList.find? (·.1 == key)).map (·.2)

/-- The output, raw linear terms, raw constant and table index of a cached single-column lookup. -/
def cachedLookup (circuit : Circuit) (layer index : Nat) :
    Option (GKRAddress × List (Nat × GKRAddress) × Nat × Nat) := do
  let (output, relation) ← (← circuit.layers[layer]?).cached_relations[index]?
  match relation with
  | .SingleColumnLookup lookup _ =>
      pure (output, lookup.input.linear_terms.toList.map (fun (coefficient, address) => (coefficient.raw.val, address)),
        lookup.input.constant.raw.val, lookup.lookup_set_index)
  | _ => none

/-! ## The cached add-sub circuit (CPU), imported with the `shared` form -/

-- circuit_defs/unrolled_circuits/add_sub_lui_auipc_mop/generated/layout.json,
-- $.layers[0].gates[16].enforced_relation.EnforceSingleMaxQuadraticConstraint.input.quadratic_terms[0]:
-- [{"BaseLayerWitness": 8}, [..., [268295646, {"BaseLayerMemory": 13}]]]
example : quadraticTerm Captures.AddSub.imported.circuit 0 16 0 1 =
    some (.BaseLayerWitness 8, 268295646, .BaseLayerMemory 13) := by decide +kernel

-- circuit_defs/unrolled_circuits/add_sub_lui_auipc_mop/generated/layout.json, $.placement_data["46"]: {"BaseLayerWitness": 20}
example : placement Captures.AddSub.imported.circuit 46 = some (.BaseLayerWitness 20) := by decide +kernel

-- circuit_defs/unrolled_circuits/add_sub_lui_auipc_mop/generated/layout.json, $.layers[0].cached_relations[8]:
-- [{"Cached": {"layer": 0, "offset": 8}}, {"SingleColumnLookup": {"relation": {"input": {"linear_terms":
-- [[1744830467, {"BaseLayerMemory": 20}], [268435454, {"BaseLayerMemory": 0}], [133099247, {"BaseLayerWitness": 16}]],
-- "constant": 0}, "lookup_set_index": 2}, ...}}]
example : cachedLookup Captures.AddSub.imported.circuit 0 8 =
    some (.Cached 0 8, [(1744830467, .BaseLayerMemory 20), (268435454, .BaseLayerMemory 0),
      (133099247, .BaseLayerWitness 16)], 0, 2) := by decide +kernel

/-! ## The cached chi circuit (worker), imported with the `shared` form -/

-- circuit_defs/keccak_chi5/generated/layout.json,
-- $.layers[0].gates[31].enforced_relation.EnforceSingleMaxQuadraticConstraint.input.linear_terms[0]:
-- [1073741816, {"BaseLayerWitness": 0}]
example : linearTerm Captures.KeccakChi5.imported.circuit 0 31 0 = some (1073741816, .BaseLayerWitness 0) := by
  decide +kernel

-- circuit_defs/keccak_chi5/generated/layout.json, $.placement_data["100"]: {"BaseLayerWitness": 46}
example : placement Captures.KeccakChi5.imported.circuit 100 = some (.BaseLayerWitness 46) := by decide +kernel

-- circuit_defs/keccak_chi5/generated/layout.json, $.layers[0].cached_relations[26]:
-- [{"Cached": {"layer": 0, "offset": 26}}, {"SingleColumnLookup": {"relation": {"input": {"linear_terms":
-- [[1073741824, {"BaseLayerMemory": 64}], [939524097, {"BaseLayerMemory": 63}]], "constant": 0},
-- "lookup_set_index": 0}, ...}}]
example : cachedLookup Captures.KeccakChi5.imported.circuit 0 26 =
    some (.Cached 0 26, [(1073741824, .BaseLayerMemory 64), (939524097, .BaseLayerMemory 63)], 0, 0) := by
  decide +kernel

/-! ## Decoder rows

Sail decodes one word. The configured decoder gives the same instruction. The decoder table of the program that
holds this word at PC 0 contains the native query of that instruction. -/

/-- A public ROM with one word at address 0. -/
def oneWordState (word : BitVec 32) : RV.State := {
  pc := 0, regFile := fun _ => 0, mem := fun _ => 0
  rom := fun address => if address.toNat < 4 then word.extractLsb' (8 * address.toNat) 8 else 0 }

/-- The public program image of that ROM for the full unsigned unrolled machine. -/
def oneWordProgram (word : BitVec 32) : List RVMachineProgramEntry :=
  (rvMachineProgramImage .unrolledFullUnsigned (oneWordState word) [0]).getD []

-- add a0, a0, a1 (0x00b50533): Sail decodes RTYPE with rs2 = x11, rs1 = x10, rd = x10 and ADD.
example : runSail (ext_decode 0x00b50533#32) resetState =
    .ok (.RTYPE (.Regidx 11, .Regidx 10, .Regidx 10, .ADD)) resetState := by
  kernel_rfl

example : (RV.decode 0x00b50533#32).map toSail = some (.RTYPE (.Regidx 11, .Regidx 10, .Regidx 10, .ADD)) := by
  kernel_rfl

/-- The native decoder fields of `add a0, a0, a1` at PC 0: PC low, PC high, rs1, rs2, rd, immediate low,
    immediate high, funct3 and mask. Mask 1 selects ADD. -/
def addFields : Vector NativeArithmetic.F 9 := #v[0, 0, 10, 11, 10, 0, 0, 0, 1]

-- The add-sub circuit omits funct3 from its decoder query.
example : NativePublicSetup.payload (.pooled .addSub) addFields = [0, 0, 10, 11, 10, 0, 0, 1] := by
  kernel_rfl

-- The add-sub decoder table contains the query at the slot of PC 0: row 0, because `offset_for_decoder_table` is 0.
example : ∃ index : NativeSetupIndex (.pooled .addSub),
    NativePublicSetup.rows (oneWordState 0x00b50533#32) (oneWordProgram 0x00b50533#32) (.pooled .addSub) 0 index =
      NativePublicSetup.payload (.pooled .addSub) addFields :=
  ⟨⟨0, by decide +kernel⟩, by kernel_rfl⟩

-- lw a1, 0(a0) (0x00052583): Sail decodes LOAD with offset 0, rs1 = x10, rd = x11, signed, 4 bytes.
example : runSail (ext_decode 0x00052583#32) resetState =
    .ok (.LOAD (0, .Regidx 10, .Regidx 11, false, 4)) resetState := by
  kernel_rfl

example : (RV.decode 0x00052583#32).map toSail = some (.LOAD (0, .Regidx 10, .Regidx 11, false, 4)) := by
  kernel_rfl

/-- The native decoder fields of `lw a1, 0(a0)` at PC 0, in the same order. LW has mask 0. -/
def loadFields : Vector NativeArithmetic.F 9 := #v[0, 0, 10, 0, 11, 0, 0, 0, 0]

-- The word-memory circuit omits funct3 and appends the decoder table identifier 46.
example : NativePublicSetup.payload (.pooled .wordMemory) loadFields = [0, 0, 10, 0, 11, 0, 0, 0, 46] := by
  kernel_rfl

-- The word-memory decoder table contains the query at the slot of PC 0: row 1048577, the `offset_for_decoder_table`.
example : ∃ index : NativeSetupIndex (.pooled .wordMemory),
    NativePublicSetup.rows (oneWordState 0x00052583#32) (oneWordProgram 0x00052583#32) (.pooled .wordMemory) 0 index =
      NativePublicSetup.payload (.pooled .wordMemory) loadFields :=
  ⟨⟨1048577, by decide +kernel⟩, by kernel_rfl⟩

end Airbender.Tests.ImportSpotChecks
