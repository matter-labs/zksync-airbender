import Airbender.Import.Parse
import Airbender.Import.Coefficients

open Airbender Lean

private def check (ok : Bool) (label : String) : IO Unit :=
  if ok then IO.println s!"PASS {label}" else throw (IO.userError label)

private def rejected {α : Type} : Except String α → Bool
  | .error _ => true
  | .ok _ => false

private def replaceField (j : Json) (name : String) (value : Json) : Except String Json := do
  let obj ← j.getObj?
  pure (Json.mkObj (obj.toArray.toList.filter (fun entry => entry.1 != name) ++ [(name, value)]))

def main : IO UInt32 := do
  try
    let source ← IO.FS.readFile "../../cs/add_sub_lui_auipc_mop_preprocessed_layout.json"
    let c ← IO.ofExcept (parseCircuit source)
    check (c.degree_2_constraints.size == 34 && c.degree_1_constraints.size == 3)
      "all native polynomial equations retained"
    check (c.witness_layout.range_check_16_lookup_expressions.size == 4 &&
      c.witness_layout.timestamp_range_check_lookup_expressions.size == 8) "all scalar ranges retained"
    check (c.logicalVariable (.MemorySubtree 15) == .ok 37 &&
      c.logicalVariable (.MemorySubtree 16) == .ok 38) "actual masked destination columns"
    for raw in [0, 1, 2147483646, 2147483647] do
      let coeff : Coefficient ← IO.ofExcept (fromJson? (toJson raw))
      check (coeff.canonical == raw % mersenne31Modulus) s!"native coefficient {raw}"
      check (toJson coeff == toJson raw) s!"exact raw coefficient roundtrip {raw}"
    check (rejected (fromJson? (toJson (2147483648 : Nat)) : Except String Coefficient))
      "reject out-of-range coefficient"
    check (rejected (fromJson? (Json.num (-1)) : Except String Coefficient)) "reject negative coefficient"
    check (rejected (fromJson? (.num 1.5) : Except String Coefficient)) "reject fractional coefficient"
    check (rejected ({c with variable_mapping := ⟨c.variable_mapping.entries.filter (fun v => v.1 != 25)⟩}.validate))
      "reject missing physical-column mapping"
    check (rejected ({c with variable_mapping := ⟨c.variable_mapping.entries.push (999, .MemorySubtree 2)⟩}.validate))
      "reject ambiguous physical-column mapping"
    check (rejected ({c with variable_mapping := ⟨c.variable_mapping.entries.push (25, .SetupSubtree 0)⟩}.validate))
      "reject duplicate logical IDs"
    check (rejected ({c with memory_layout := {c.memory_layout with total_width := 0}}.validate)) "reject out-of-bounds native columns"
    check (rejected ({c with degree_2_constraints := c.degree_2_constraints.extract 1 c.degree_2_constraints.size}.validate))
      "reject omitted native Boolean constraint"
    check (rejected ({c with witness_layout := {c.witness_layout with
      range_check_16_lookup_expressions := c.witness_layout.range_check_16_lookup_expressions.extract 1 4}}.validate))
      "reject omitted native scalar range"
    let clocks ← IO.ofExcept c.traceColumns
    let ports ← IO.ofExcept c.memoryPorts
    check (clocks.execute == 4 && clocks.initialPC == #v[0,1] && clocks.finalTime == #v[15,16])
      "native machine-state placement"
    check (ports.size == 3 && ports[2]?.any (fun port => port.writeValue == some (.u16 #v[37,38])))
      "native actual-write metadata"
    check (rejected ({c with memory_queries_timestamp_comparison_aux_vars := #[]}.traceColumns))
      "reject incomplete native borrow metadata"
    check (rejected ({c with memory_layout := {c.memory_layout with
      machine_state_layout := none}}.traceColumns)) "reject missing native final state"
    check (rejected (c.memoryColumns ⟨0,2⟩ 2)) "reject wrong native column-group extent"
    check (rejected (c.memoryColumns ⟨c.memory_layout.total_width,1⟩ 2))
      "reject native multi-limb group overflow"
    let decoder ← IO.ofExcept c.decoderColumns
    check (decoder == ⟨5,6,7,8,#v[9,10],11,12⟩) "native ten-column decoder placement"
    let some state := c.memory_layout.intermediate_state_layout
      | throw (IO.userError "missing test decoder state")
    let withState := fun state => {c with memory_layout :=
      {c.memory_layout with intermediate_state_layout := some state}}
    check (rejected ((withState {state with rd_is_zero := ⟨0,2⟩}).decoderColumns))
      "reject decoder zero-flag group extent"
    check (rejected ((withState {state with imm := ⟨c.witness_layout.total_width - 1,1⟩}).decoderColumns))
      "reject decoder immediate group overflow"
    check (rejected ((withState {state with funct7 := ⟨0,1⟩}).decoderColumns))
      "reject unsupported decoder funct7 field"
    check (rejected ((withState {state with circuit_family := ⟨0,1⟩}).decoderColumns))
      "reject unsupported decoder family field"
    check (rejected ((withState {state with circuit_family_extra_mask := .SetupSubtree 0}).decoderColumns))
      "reject unmapped decoder packed mask"
    let json ← IO.ofExcept (Json.parse source)
    let linked ← IO.ofExcept (replaceField json "state_linkage_constraints" (.arr #[.arr #[]]))
    check (rejected (parseCircuit linked.compress)) "reject unsupported inter-row linkage"
    let witness ← IO.ofExcept (json.getObjVal? "witness_layout")
    let lookup ← IO.ofExcept (replaceField witness "width_3_lookups" (.arr #[.null]))
    let lookup ← IO.ofExcept (replaceField json "witness_layout" lookup)
    check (rejected (parseCircuit lookup.compress)) "reject unsupported fixed lookups"
    let badRange := {c.witness_layout with range_check_8_columns := ⟨0, 1⟩}
    check (rejected ({c with witness_layout := badRange}.validate)) "reject unsupported byte ranges"
    check (rejected (parseCircuit "{}")) "reject missing required schema"
    return (0 : UInt32)
  catch error =>
    IO.eprintln s!"FAIL {error}"
    return (1 : UInt32)
