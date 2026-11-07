import Human.Import.Parse
import Human.Helpers.Memory.InitsTeardownsColumns
import Lean

/-! Import of the inits/teardowns sets: the standalone circuit
    (`cs/src/gkr_compiler/inits_and_teardowns.rs`) and the sets inlined into a family
    circuit (`cs/src/gkr_compiler/inits_and_teardowns_inline.rs`). Kept out of
    `Parse`/`Embed` so that adding it does not rebuild every other artifact. -/

namespace Airbender
open Lean Elab Command

/-- The logical variable placed at memory column `n`; unique, as `Parse`'s
    (private) `Circuit.logicalVariable` requires. Teardown columns are never scratch aliases. -/
private def Circuit.teardownVariable (c : Circuit) (address : GKRAddress) : Except String Nat := do
  let .BaseLayerMemory n := address | throw "teardown column must be a memory column"
  unless n < c.memory_layout.total_width do throw "teardown column outside memory layout"
  match (c.placement_data.entries.filter fun (_, a) => a == address).toList with
  | [(v, _)] => pure v
  | _ => throw s!"teardown column must have exactly one logical variable: {n}"

/-- The two logical variables of a limb pair. -/
private def Circuit.teardownPair (c : Circuit) (columns : Fixed 2 GKRAddress) : Except String (Vector Nat 2) := do
  let lo ← c.teardownVariable (columns.values[0]'(by rw [columns.size_eq]; decide))
  let hi ← c.teardownVariable (columns.values[1]'(by rw [columns.size_eq]; decide))
  pure #v[lo, hi]

/-- Raw memory column index of a teardown column. -/
private def teardownColumn (address : GKRAddress) : Except String Nat := do
  let .BaseLayerMemory n := address | throw "teardown column must be a memory column"
  pure n

/-- Resolve the inits/teardowns sets. Refuses unless `trace_len` is a power of two,
    the word bits are at most 3 (as Rust asserts) with `log2 trace_len + word bits` in
    `[16, 32]`, the set count is a power of two at least two, and the layer-0
    `InitsOrTeardownsInitialPair` gates are exactly, for each pair `k`, one `Init` gate and
    one `Teardown` gate with set indices `[2k, 2k+1]`, setup `[InitsAndTeardownsLow,
    InitsAndTeardownsHigh]`, and (for `Teardown`) the timestamp/value columns of sets
    `2k`, `2k+1` in that order. With `standalone`, also refuses any machine, delegation,
    decoder or RAM-access metadata, any constraint or lookup, any witness column, any
    memory column that is not a teardown column, and any other layer-0 gate. -/
def Circuit.initsTeardownsLayout (c : Circuit) (standalone : Bool) :
    Except String InitsTeardowns.Layout := do
  let layout := c.memory_layout
  let some wordBits := layout.inits_and_teardowns_word_bits | throw "inits/teardowns word bits are missing"
  let wordBits := wordBits.val
  let traceLog := c.trace_len.log2
  unless c.trace_len == 2 ^ traceLog do throw "trace length must be a power of two"
  unless wordBits ≤ 3 && 16 ≤ traceLog + wordBits && traceLog + wordBits ≤ 32 do
    throw "unsupported inits/teardowns word bits or trace length"
  let count := layout.teardown_sets.size
  unless 2 ≤ count && count == 2 ^ count.log2 do throw "set count must be a power of two, at least two"
  let mut sets : Array InitsTeardowns.TeardownSet := #[]
  let mut seen : Array Nat := #[]
  for (timestamp, value) in layout.teardown_sets do
    let value ← c.teardownPair value
    let timestamp ← c.teardownPair timestamp
    for v in value.toArray ++ timestamp.toArray do
      if seen.contains v then throw "teardown columns must be distinct"
      seen := seen.push v
    sets := sets.push (⟨value, timestamp⟩ : InitsTeardowns.TeardownSet)
  let setup : Array GKRAddress := #[.VirtualSetup .InitsAndTeardownsLow, .VirtualSetup .InitsAndTeardownsHigh]
  let mut found : Array (Bool × Array Nat × Array Nat) := #[]
  for l in c.layers do
    for g in l.gates ++ l.gates_with_external_connections do
      match g.enforced_relation with
      | .InitsOrTeardownsInitialPair tv gateSetup _ indices =>
        unless l.layer == 0 && g.output_layer == 1 do throw "inits/teardowns gate outside layer 0"
        unless gateSetup.values == setup do throw "inits/teardowns gate has an unexpected setup"
        match tv with
        | .Init => found := found.push (true, indices.values, #[])
        | .Teardown lt lv rt rv =>
          found := found.push (false, indices.values, lt.values ++ lv.values ++ rt.values ++ rv.values)
      | _ => if standalone && l.layer == 0 then throw "standalone inits/teardowns has another layer-0 gate"
  unless found.size == count do throw "inits/teardowns gate count differs from the sets"
  for k in [:count / 2] do
    let some (lt, lv) := layout.teardown_sets[2 * k]? | throw "inits/teardowns set is missing"
    let some (rt, rv) := layout.teardown_sets[2 * k + 1]? | throw "inits/teardowns set is missing"
    let columns ← (lt.values ++ lv.values ++ rt.values ++ rv.values).mapM teardownColumn
    unless found.contains (true, #[2 * k, 2 * k + 1], #[]) do throw "inits/teardowns init gate is missing"
    unless found.contains (false, #[2 * k, 2 * k + 1], columns) do throw "inits/teardowns teardown gate is missing"
  if standalone then
    unless layout.machine_state.isNone && layout.delegation_state.isNone && layout.decoder_input.isNone &&
        layout.ram_access_sets.isEmpty && layout.indirect_access_variable_offsets.isEmpty do
      throw "standalone inits/teardowns cannot carry machine, delegation, decoder or RAM-access metadata"
    unless c.structured_statements.isEmpty && c.degree_1_constraints.isEmpty &&
        c.degree_2_constraints.isEmpty && c.generic_lookups.isEmpty && c.num_generic_lookups == 0 &&
        c.range_check_16_lookup_expressions.isEmpty && c.timestamp_range_check_lookup_expressions.isEmpty &&
        c.witness_layout.total_width == 0 && layout.total_width == 4 * count do
      throw "standalone inits/teardowns cannot carry constraints, lookups or other columns"
  pure ⟨traceLog, wordBits, sets⟩

/-- `import_inits_teardowns name from "path" [standalone]` defines
    `name : InitsTeardowns.Layout` from the artifact's inits/teardowns sets
    (`Circuit.initsTeardownsLayout`). -/
elab "import_inits_teardowns " name:ident " from " path:str standalone:(" standalone")? : command => do
  let source ← IO.FS.readFile path.getString
  let c ← match parseCircuit source with
    | .ok c => pure c
    | .error e => throwError "circuit import failed: {e}"
  let layout ← match c.initsTeardownsLayout standalone.isSome with
    | .ok layout => pure layout
    | .error e => throwError "inits/teardowns import failed: {e}"
  let pairSyntax := fun (columns : Vector Nat 2) =>
    `(#v[$(quote columns[0]), $(quote columns[1])])
  let setTerms ← layout.sets.toList.mapM fun set => do
    `(Airbender.InitsTeardowns.TeardownSet.mk $(← pairSyntax set.value) $(← pairSyntax set.timestamp))
  let setTerms := setTerms.toArray
  elabCommand (← `(def $name : Airbender.InitsTeardowns.Layout :=
    ⟨$(quote layout.traceLog), $(quote layout.wordBits), #[$[$setTerms],*]⟩))

end Airbender
