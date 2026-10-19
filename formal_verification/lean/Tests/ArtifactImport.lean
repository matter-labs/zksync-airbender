import Airbender.Import.Parse
import Airbender.Import.Coefficients
import Airbender.Import.Setup

open Airbender Lean

private def check (ok : Bool) (label : String) : IO Unit :=
  if ok then IO.println s!"PASS {label}" else throw (IO.userError label)

private def rejected {α : Type} : Except String α → Bool
  | .error _ => true
  | .ok _ => false

private def replaceField (j : Json) (name : String) (value : Json) : Except String Json := do
  let obj ← j.getObj?
  pure (Json.mkObj (obj.toArray.toList.filter (fun entry => entry.1 != name) ++ [(name, value)]))

private def scalarChecks (setupSource : String) : IO Unit := do
  let scalarSource ← IO.FS.readFile "artifacts/setup/scalars-native.json"
  let scalar ← IO.ofExcept (Setup.parseScalars scalarSource)
  check (scalar.range16.length == 65536 && scalar.timestamp19.length == 524288)
    "actual native range16/timestamp19 scalar extents"
  check (rejected ({scalar with version := 2}.validate)) "reject scalar export version"
  check (rejected ({scalar with field_modulus := 2013265921}.validate)) "reject v3 scalar field"
  check (rejected ({scalar with profile := "timestamp19"}.validate)) "reject changed scalar profile"
  check (rejected ({scalar with timestamp19 := {scalar.timestamp19 with length := 524287}}.validate))
    "reject truncated timestamp prefix"
  check (rejected ({scalar with timestamp19 := {scalar.timestamp19 with columns := #[]}}.validate))
    "reject missing timestamp column"
  check (rejected ({scalar with timestamp19 := {scalar.timestamp19 with columns :=
    scalar.timestamp19.columns ++ scalar.timestamp19.columns}}.validate)) "reject extra timestamp column"
  check (rejected ({scalar with timestamp19 := {scalar.timestamp19 with columns :=
    #[⟨#[.affine 524287 0 1]⟩]}}.validate)) "reject incomplete compressed timestamp column"
  check (rejected ({scalar with timestamp19 := {scalar.timestamp19 with columns :=
    #[⟨#[.affine 524288 2147483647 0]⟩]}}.validate)) "reject noncanonical timestamp data"
  let scalarJson ← IO.ofExcept (Json.parse scalarSource)
  let unknownScalar ← IO.ofExcept (replaceField scalarJson "invented" (.bool true))
  check (rejected (Setup.parseScalars unknownScalar.compress)) "reject unknown scalar export field"
  let timestampJson ← IO.ofExcept (scalarJson.getObjVal? "timestamp19")
  let extraMatrix ← IO.ofExcept (replaceField timestampJson "invented" (.bool true))
  let extraScalar ← IO.ofExcept (replaceField scalarJson "timestamp19" extraMatrix)
  check (rejected (Setup.parseScalars extraScalar.compress)) "reject unknown scalar matrix field"
  let columns ← IO.ofExcept ((← IO.ofExcept (timestampJson.getObjVal? "columns")).getArr?)
  let extraColumn ← IO.ofExcept (replaceField columns[0]! "invented" (.bool true))
  let extraMatrix ← IO.ofExcept (replaceField timestampJson "columns" (Json.arr #[extraColumn]))
  let extraScalar ← IO.ofExcept (replaceField scalarJson "timestamp19" extraMatrix)
  check (rejected (Setup.parseScalars extraScalar.compress)) "reject unknown scalar column field"
  check (rejected (Setup.parseScalars setupSource)) "reject program artifact as scalar export"
  check (rejected (Setup.parse scalarSource)) "reject scalar artifact as program export"

private def decoderChecks (setupSource : String) : IO Unit := do
  let source ← IO.FS.readFile "artifacts/setup/arithmetic-native.json"
  let artifact ← IO.ofExcept (Setup.parseDecoder source)
  check (artifact.text_words == 7 && artifact.decoder.length == 1048576 &&
    artifact.decoder.columns.size == 10) "actual native arithmetic decoder extent"
  check (rejected ({artifact with version := 2}.validate)) "reject decoder export version"
  check (rejected ({artifact with field_modulus := 2013265921}.validate)) "reject v3 decoder export field"
  check (rejected ({artifact with family := "load_store_word_only"}.validate)) "reject changed decoder family"
  check (rejected ({artifact with text_words := 1048577}.validate)) "reject oversized decoder text"
  check (rejected ({artifact with text_words := 6}.validate)) "reject incomplete decoder text extent"
  check (rejected ({artifact with text := ⟨#[.dense #[4294967296]]⟩, text_words := 1}.validate))
    "reject oversized decoder input word"
  check (rejected ({artifact with decoder := {artifact.decoder with length := 1048575}}.validate))
    "reject truncated arithmetic decoder"
  check (rejected ({artifact with decoder := {artifact.decoder with columns :=
    (artifact.decoder.columns.extract 0 9)}}.validate)) "reject missing arithmetic decoder column"
  check (rejected ({artifact with decoder := {artifact.decoder with columns :=
    (artifact.decoder.columns.push ⟨#[.affine 1048576 0 0]⟩)}}.validate)) "reject extra arithmetic decoder column"
  check (rejected ({artifact with decoder := {artifact.decoder with columns :=
    (artifact.decoder.columns.set! 0 ⟨#[.affine 1048575 0 0]⟩)}}.validate)) "reject incomplete decoder column"
  check (rejected ({artifact with decoder := {artifact.decoder with columns :=
    (artifact.decoder.columns.set! 0 ⟨#[.affine 1048576 2147483647 0]⟩)}}.validate))
    "reject noncanonical arithmetic decoder cell"
  let json ← IO.ofExcept (Json.parse source)
  let unknown ← IO.ofExcept (replaceField json "invented" (.bool true))
  check (rejected (Setup.parseDecoder unknown.compress)) "reject unknown decoder export field"
  let matrix ← IO.ofExcept (json.getObjVal? "decoder")
  let extraMatrix ← IO.ofExcept (replaceField matrix "invented" (.bool true))
  let unknown ← IO.ofExcept (replaceField json "decoder" extraMatrix)
  check (rejected (Setup.parseDecoder unknown.compress)) "reject unknown decoder matrix field"
  let columns ← IO.ofExcept ((← IO.ofExcept (matrix.getObjVal? "columns")).getArr?)
  let extraColumn ← IO.ofExcept (replaceField columns[0]! "invented" (.bool true))
  let extraMatrix ← IO.ofExcept (replaceField matrix "columns" (Json.arr (columns.set! 0 extraColumn)))
  let unknown ← IO.ofExcept (replaceField json "decoder" extraMatrix)
  check (rejected (Setup.parseDecoder unknown.compress)) "reject unknown decoder column field"
  check (rejected (Setup.parseDecoder setupSource)) "reject program artifact as decoder export"
  check (rejected (Setup.parse source)) "reject decoder artifact as program export"
  check (rejected (Setup.parseScalars source)) "reject decoder artifact as scalar export"
  check (rejected (Setup.parseDecoder (← IO.FS.readFile "artifacts/setup/scalars-native.json")))
    "reject scalar artifact as decoder export"

private def controlDecoderChecks : IO Unit := do
  let source ← IO.FS.readFile "artifacts/setup/jump-decoder-native.json"
  let artifact ← IO.ofExcept (Setup.parseControlDecoder source)
  check (artifact.text_words == 3 && artifact.decoder.length == 1048576 &&
    artifact.decoder.columns.size == 10) "actual native signed control decoder extent"
  check (rejected (Setup.parseDecoder source)) "reject control decoder as arithmetic"
  check (rejected (Setup.parseControlDecoder (← IO.FS.readFile "artifacts/setup/arithmetic-native.json")))
    "reject arithmetic decoder as control"
  check (rejected (Setup.parseControlDecoder (← IO.FS.readFile "artifacts/setup/jump-control-native.json")))
    "reject fixed control tables as decoder"
  let json ← IO.ofExcept (Json.parse source)
  for (key, value, label) in [
      ("version", toJson (2 : Nat), "reject control decoder version"),
      ("field_modulus", toJson (2013265921 : Nat), "reject v3 control decoder field"),
      ("family", toJson "jump_branch_slt_unsigned", "reject unsigned-only control decoder"),
      ("text_words", toJson (1048577 : Nat), "reject oversized control text"),
      ("text_words", toJson (2 : Nat), "reject incomplete control text"),
      ("invented", Json.bool true, "reject unknown control decoder field")] do
    let changed ← IO.ofExcept (replaceField json key value)
    check (rejected (Setup.parseControlDecoder changed.compress)) label
  let matrix ← IO.ofExcept (json.getObjVal? "decoder")
  let changed ← IO.ofExcept (replaceField matrix "length" (toJson (1048575 : Nat)))
  let changed ← IO.ofExcept (replaceField json "decoder" changed)
  check (rejected (Setup.parseControlDecoder changed.compress)) "reject truncated control decoder"
  let columns ← IO.ofExcept ((← IO.ofExcept (matrix.getObjVal? "columns")).getArr?)
  let changed ← IO.ofExcept (replaceField matrix "columns" (Json.arr (columns.extract 0 9)))
  let changed ← IO.ofExcept (replaceField json "decoder" changed)
  check (rejected (Setup.parseControlDecoder changed.compress)) "reject missing control decoder column"
  let bad ← IO.ofExcept (Json.parse "{\"blocks\":[{\"kind\":\"affine\",\"length\":1048576,\"first\":2147483647,\"step\":0}]}")
  let changed ← IO.ofExcept (replaceField matrix "columns" (Json.arr (columns.set! 0 bad)))
  let changed ← IO.ofExcept (replaceField json "decoder" changed)
  check (rejected (Setup.parseControlDecoder changed.compress)) "reject noncanonical control decoder cell"

private def decoderPaddingChecks : IO Unit := do
  let source ← IO.FS.readFile "artifacts/setup/decoder-padding-native.json"
  let artifact ← IO.ofExcept (Setup.parseDecoderPadding source)
  check (artifact.row.size == 10) "actual native decoder padding extent"
  check (rejected ({artifact with version := 2}.validate)) "reject decoder padding version"
  check (rejected ({artifact with field_modulus := 2013265921}.validate)) "reject v3 padding field"
  check (rejected ({artifact with profile := "zero_padding"}.validate)) "reject changed padding profile"
  check (rejected ({artifact with row := artifact.row.extract 0 9}.validate)) "reject short padding row"
  check (rejected ({artifact with row := artifact.row.push 0}.validate)) "reject long padding row"
  check (rejected ({artifact with row := artifact.row.set! 0 2147483647}.validate))
    "reject noncanonical padding value"
  let json ← IO.ofExcept (Json.parse source)
  let unknown ← IO.ofExcept (replaceField json "invented" (.bool true))
  check (rejected (Setup.parseDecoderPadding unknown.compress)) "reject unknown padding field"
  check (rejected (Setup.parse source)) "reject padding artifact as program export"
  check (rejected (Setup.parseScalars source)) "reject padding artifact as scalar export"
  check (rejected (Setup.parseDecoder source)) "reject padding artifact as decoder prefix export"
  check (rejected (Setup.parseDecoderPadding (← IO.FS.readFile "artifacts/setup/arithmetic-native.json")))
    "reject decoder prefix as padding export"

private def controlChecks : IO Unit := do
  let source ← IO.FS.readFile "artifacts/setup/jump-control-native.json"
  let artifact ← IO.ofExcept (Setup.parseControl source)
  let some cleanup := artifact.tables[0]? | throw (IO.userError "missing native cleanup region")
  let some conditional := artifact.tables[1]? | throw (IO.userError "missing native conditional region")
  check (artifact.generic_rows == 65664 && artifact.tables.size == 2 &&
    cleanup.id == 17 && conditional.id == 43)
    "actual native control table extent and tags"
  check (rejected ({artifact with version := 2}.validate)) "reject control export version"
  check (rejected ({artifact with field_modulus := 2013265921}.validate)) "reject v3 control field"
  check (rejected ({artifact with profile := "range16_timestamp19"}.validate)) "reject changed control profile"
  check (rejected ({artifact with generic_rows := 65665}.validate)) "reject invented control dummy row"
  check (rejected ({artifact with tables := artifact.tables.extract 0 1}.validate)) "reject missing control region"
  check (rejected ({artifact with tables := artifact.tables.push cleanup}.validate))
    "reject extra control region"
  check (rejected ({artifact with tables := #[{cleanup with id := 0}, conditional]}.validate))
    "reject changed native cleanup tag"
  check (rejected ({artifact with tables := #[cleanup, {conditional with offset := 65537}]}.validate))
    "reject shifted native conditional region"
  check (rejected ({artifact with tables := #[conditional, cleanup]}.validate)) "reject reordered native control regions"
  check (rejected ({artifact with tables := #[cleanup, {conditional with data :=
    {conditional.data with length := 127}}]}.validate)) "reject truncated conditional extent"
  check (rejected ({artifact with tables := #[{cleanup with data :=
    {cleanup.data with columns := cleanup.data.columns.extract 0 3}}, conditional]}.validate))
    "reject missing native control tag column"
  check (rejected ({artifact with tables := #[{cleanup with data :=
    {cleanup.data with columns := cleanup.data.columns.set! 0 ⟨#[.affine 65535 0 1]⟩}}, conditional]}.validate))
    "reject incomplete native cleanup column"
  check (rejected ({artifact with tables := #[{cleanup with data :=
    {cleanup.data with columns := cleanup.data.columns.set! 0 ⟨#[.affine 65536 2147483647 0]⟩}}, conditional]}.validate))
    "reject noncanonical native control field"
  let json ← IO.ofExcept (Json.parse source)
  let unknown ← IO.ofExcept (replaceField json "invented" (.bool true))
  check (rejected (Setup.parseControl unknown.compress)) "reject unknown control export field"
  let regions ← IO.ofExcept ((← IO.ofExcept (json.getObjVal? "tables")).getArr?)
  let region ← IO.ofExcept (replaceField regions[0]! "invented" (.bool true))
  let unknown ← IO.ofExcept (replaceField json "tables" (Json.arr (regions.set! 0 region)))
  check (rejected (Setup.parseControl unknown.compress)) "reject unknown control region field"
  let matrix ← IO.ofExcept (regions[0]!.getObjVal? "data")
  let extra ← IO.ofExcept (replaceField matrix "invented" (.bool true))
  let region ← IO.ofExcept (replaceField regions[0]! "data" extra)
  let unknown ← IO.ofExcept (replaceField json "tables" (Json.arr (regions.set! 0 region)))
  check (rejected (Setup.parseControl unknown.compress)) "reject unknown control matrix field"
  check (rejected (Setup.parse source)) "reject control artifact as program export"
  check (rejected (Setup.parseScalars source)) "reject control artifact as scalar export"
  check (rejected (Setup.parseControl (← IO.FS.readFile "artifacts/setup/scalars-native.json")))
    "reject scalar export as control artifact"
  let circuit ← IO.ofExcept (parseCircuit (← IO.FS.readFile "../../cs/jump_branch_slt_preprocessed_layout.json"))
  check (circuit.degree_2_constraints.size == 33 && circuit.degree_1_constraints.size == 3 &&
    circuit.witness_layout.width_3_lookups.size == 2 &&
    circuit.witness_layout.range_check_16_lookup_expressions.size == 6 &&
    circuit.witness_layout.timestamp_range_check_lookup_expressions.size == 8)
    "all native jump branch slt equations and queries retained"
  check (rejected ({circuit with total_tables_size := 65665}.validate)) "reject control layout dummy extent"
  check (rejected ({circuit with table_offsets := circuit.table_offsets.set! 43 65537}.validate))
    "reject control layout table offset"
  let some first := circuit.witness_layout.width_3_lookups[0]? | throw (IO.userError "missing control query")
  let some second := circuit.witness_layout.width_3_lookups[1]? | throw (IO.userError "missing cleanup query")
  check (rejected ({circuit with witness_layout := {circuit.witness_layout with width_3_lookups :=
    #[{first with table_index := .Constant .RomRead}, second]}}.validate)) "reject mixed native lookup profiles"
  check (rejected ({circuit with witness_layout := {circuit.witness_layout with width_3_lookups :=
    #[first, first]}}.validate)) "reject repeated native control table"
  check (rejected ({circuit with witness_layout := {circuit.witness_layout with width_3_lookups :=
    #[second, first]}}.validate)) "reject reversed control lookup profile"
  check (rejected ({circuit with witness_layout := {circuit.witness_layout with width_3_lookups :=
    #[{first with input_columns := first.input_columns.extract 0 2}, second]}}.validate))
    "reject two-column v3-shaped control query"

private def mulDivChecks : IO Unit := do
  let source ← IO.FS.readFile "../../cs/mul_div_unsigned_preprocessed_layout.json"
  let c ← IO.ofExcept (parseCircuit source)
  check (c.degree_2_constraints.size == 43 && c.degree_1_constraints.size == 6)
    "all native unsigned mul/div equations retained"
  check (c.witness_layout.range_check_8_columns.start == 9 &&
    c.witness_layout.range_check_8_columns.num_elements == 11 &&
    c.witness_layout.width_3_lookups.size == 6 &&
    c.witness_layout.range_check_16_lookup_expressions.size == 6 &&
    c.witness_layout.timestamp_range_check_lookup_expressions.size == 8)
    "all eleven byte columns and six paired native fixed queries retained"
  check ((← IO.ofExcept c.setupColumns) == ⟨16777216,16,0,1,2,1,6,1048576,65536⟩)
    "native unsigned mul/div tagged setup placement"
  check ((← IO.ofExcept c.decoderColumns) == ⟨5,6,7,8,#v[9,10],11,12⟩)
    "native unsigned mul/div decoder placement"
  check (c.scratch_space_size_for_witness_gen == 2 &&
    c.variable_mapping.entries.contains (27,.OptimizedOut 0) &&
    c.variable_mapping.entries.contains (28,.OptimizedOut 1)) "native optimized-out scratch metadata retained"
  check (rejected (c.logicalVariable (.OptimizedOut 0))) "reject consuming optimized-out column"
  check (rejected ({c with scratch_space_size_for_witness_gen := 1}.validate))
    "reject optimized-out scratch overflow"
  check (rejected ({c with variable_mapping := ⟨c.variable_mapping.entries.push (999,.OptimizedOut 0)⟩}.validate))
    "reject ambiguous optimized-out scratch mapping"
  let one : Coefficient ← IO.ofExcept (fromJson? (toJson (1 : Nat)))
  let zero : Coefficient ← IO.ofExcept (fromJson? (toJson (0 : Nat)))
  check (rejected ({c with degree_1_constraints := (c.degree_1_constraints.push
    ⟨#[(one,.OptimizedOut 0)],zero⟩)}.validate)) "reject optimized-out equation input"
  let withQueries := fun queries => {c with witness_layout :=
    {c.witness_layout with width_3_lookups := queries}}
  let some first := c.witness_layout.width_3_lookups[0]? | throw (IO.userError "missing native byte query")
  let some second := c.witness_layout.width_3_lookups[1]? | throw (IO.userError "missing second native byte query")
  let some last := c.witness_layout.width_3_lookups[5]? | throw (IO.userError "missing odd native byte query")
  let changedFirst := fun query => withQueries (c.witness_layout.width_3_lookups.set! 0 query)
  check (rejected ((withQueries (c.witness_layout.width_3_lookups.extract 0 5)).validate))
    "reject omitted paired native byte query"
  check (rejected ((changedFirst second).validate)) "reject repeated paired byte query"
  check (rejected ((changedFirst {first with input_columns := first.input_columns.extract 0 2}).validate))
    "reject short native byte tuple"
  check (rejected ((changedFirst {first with input_columns := first.input_columns.set! 2 (.Expression ⟨#[],one⟩)}).validate))
    "reject nonzero third byte-query padding"
  check (rejected ((changedFirst {first with input_columns := first.input_columns.set! 0 (.Variable (.OptimizedOut 0))}).validate))
    "reject optimized-out fixed query input"
  check (rejected ((changedFirst {first with table_index := .Constant .JumpCleanupOffset}).validate))
    "reject mixed unsigned mul/div fixed profile"
  check (rejected ((withQueries (c.witness_layout.width_3_lookups.set! 5
    {last with input_columns := last.input_columns.set! 1 (.Expression ⟨#[],one⟩)})).validate))
    "reject nonzero odd-byte second padding"
  check (rejected ({c with witness_layout := {c.witness_layout with range_check_8_columns := ⟨9,10⟩}}.validate))
    "reject unaccounted native byte query"
  check (rejected ({c with witness_layout := {c.witness_layout with range_check_8_columns := ⟨9,12⟩}}.validate))
    "reject declared byte without native query input"
  check (rejected ({c with witness_layout := {c.witness_layout with range_check_8_columns := ⟨c.witness_layout.total_width,11⟩}}.validate))
    "reject native byte range outside witness bank"
  check (rejected ({c with variable_mapping := ⟨c.variable_mapping.entries.filter (fun entry => entry.1 != 35)⟩}.validate))
    "reject unmapped native byte input"
  check (rejected ({c with witness_layout := {c.witness_layout with range_check_16_lookup_expressions :=
    (c.witness_layout.range_check_16_lookup_expressions.push (.Variable (.OptimizedOut 0)))}}.validate))
    "reject optimized-out scalar query input"
  check (rejected ({c with total_tables_size := 65535}.validate)) "reject truncated native byte setup"
  check (rejected ({c with table_offsets := c.table_offsets.set! 9 65535}.validate))
    "reject shifted native byte setup offset"
  let fixedSource ← IO.FS.readFile "artifacts/setup/mul-div-small-range-native.json"
  let fixed ← IO.ofExcept (Setup.parseSmallRange fixedSource)
  check (fixed.generic_rows == 65536 && fixed.tables.map (·.id) == #[8])
    "actual native byte-table tagged export geometry"
  check (rejected (Setup.parseControl fixedSource)) "reject byte tables as control tables"
  check (rejected (Setup.parseSmallRange (← IO.FS.readFile "artifacts/setup/jump-control-native.json")))
    "reject control tables as byte tables"
  let json ← IO.ofExcept (Json.parse fixedSource)
  for (key,value,label) in [
      ("version",toJson (2 : Nat),"reject byte-table export version"),
      ("field_modulus",toJson (2013265921 : Nat),"reject v3 byte-table field"),
      ("profile",toJson "jump_branch_slt_fixed","reject changed byte-table profile"),
      ("generic_rows",toJson (65535 : Nat),"reject byte-table export extent"),
      ("invented",Json.bool true,"reject unknown byte-table export field")] do
    let changed ← IO.ofExcept (replaceField json key value)
    check (rejected (Setup.parseSmallRange changed.compress)) label
  let tables ← IO.ofExcept ((← IO.ofExcept (json.getObjVal? "tables")).getArr?)
  let region := tables[0]!
  for (key,value,label) in [("id",toJson (9 : Nat),"reject changed native byte-table tag"),
      ("offset",toJson (1 : Nat),"reject shifted native byte-table export")] do
    let changed ← IO.ofExcept (replaceField region key value)
    let changed ← IO.ofExcept (replaceField json "tables" (.arr #[changed]))
    check (rejected (Setup.parseSmallRange changed.compress)) label

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
    check (rejected ({c with witness_layout := badRange}.validate)) "reject byte columns without native fixed queries"
    let wordSource ← IO.FS.readFile "../../cs/word_only_load_store_preprocessed_layout.json"
    let word ← IO.ofExcept (parseCircuit wordSource)
    check (word.degree_2_constraints.size == 31 && word.degree_1_constraints.size == 4)
      "all native word-memory polynomials retained"
    check (word.witness_layout.width_3_lookups.size == 2 &&
      word.witness_layout.range_check_16_lookup_expressions.size == 2 &&
      word.witness_layout.timestamp_range_check_lookup_expressions.size == 8)
      "all native word-memory fixed and range queries retained"
    let wordPorts ← IO.ofExcept word.memoryPorts
    check (wordPorts[1]?.any (fun port => port.address == .mixed 12 true #v[28,29]) &&
      wordPorts[2]?.any (fun port => port.address == .mixed 32 true #v[33,34] &&
        port.writeValue == some (.u16 #v[37,38]))) "native word-memory mixed ports"
    check ((← IO.ofExcept word.decoderColumns) == ⟨5,6,7,8,#v[9,10],11,12⟩)
      "native word-memory decoder flag and mask"
    let some query := word.witness_layout.width_3_lookups[0]?
      | throw (IO.userError "missing native fixed lookup")
    let withQueries := fun queries => {word with witness_layout :=
      {word.witness_layout with width_3_lookups := queries}}
    check (rejected ((withQueries #[{query with input_columns := query.input_columns.extract 0 2}]).validate))
      "reject short fixed lookup"
    check (rejected ((withQueries #[{query with input_columns := query.input_columns.push (.Variable (.WitnessSubtree 0))}]).validate))
      "reject wide fixed lookup"
    check (rejected ((withQueries #[{query with input_columns :=
      #[.Variable (.WitnessSubtree 999), .Variable (.WitnessSubtree 19), .Variable (.WitnessSubtree 20)]}]).validate))
      "reject out-of-layout fixed lookup column"
    check (rejected ((withQueries #[{query with input_columns :=
      #[.Expression ⟨#[(⟨⟨1, by decide⟩⟩, .SetupSubtree 0)], ⟨⟨0, by decide⟩⟩⟩,
        .Variable (.WitnessSubtree 19), .Variable (.WitnessSubtree 20)]}]).validate))
      "reject unmapped fixed lookup expression"
    check (rejected (fromJson? (Json.mkObj [("Constant", toJson "Xor")]) :
      Except String FixedTableIndex)) "reject unsupported fixed table"
    check (rejected (fromJson? (Json.mkObj [("Variable", toJson (0 : Nat))]) :
      Except String FixedTableIndex)) "reject dynamic fixed-table selection"
    check ((← IO.ofExcept c.setupColumns) == ⟨16777216,12,0,1,2,0,2,1048576,0⟩)
      "native arithmetic physical setup placement"
    check ((← IO.ofExcept word.setupColumns) == ⟨16777216,16,0,1,2,1,6,1048576,1114113⟩)
      "native word-memory tagged setup placement"
    check (rejected ({word with trace_len := 1048576}.validate)) "reject changed setup trace extent"
    check (rejected ({word with executor_family_decoder_table_size := 0}.validate))
      "reject missing decoder setup extent"
    check (rejected ({word with setup_layout := {word.setup_layout with
      timestamp_setup_columns := ⟨0,1⟩}}.validate)) "reject unsupported timestamp setup group"
    check (rejected ({word with setup_layout := {word.setup_layout with
      range_check_16_setup_column := ⟨1,1⟩}}.validate)) "reject overlapping scalar setup columns"
    check (rejected ({word with setup_layout := {word.setup_layout with
      timestamp_range_check_setup_column := ⟨1,2⟩}}.validate)) "reject scalar setup group extent"
    check (rejected ({word with setup_layout := {word.setup_layout with
      generic_lookup_setup_columns := ⟨2,2⟩}}.validate)) "reject multiple generic setup groups"
    check (rejected ({word with setup_layout := {word.setup_layout with
      preprocessed_decoder_setup_columns := ⟨5,1⟩}}.validate)) "reject decoder overlap with native tag"
    check (rejected ({word with setup_layout := {word.setup_layout with
      preprocessed_decoder_setup_columns := ⟨6,2⟩}}.validate)) "reject multiple decoder setup groups"
    check (rejected ({word with setup_layout := {word.setup_layout with total_width := 17}}.validate))
      "reject unaccounted setup columns"
    check (rejected ({word with total_tables_size := 1114112}.validate)) "reject missing native dummy row"
    check (rejected ({word with table_offsets := #[]}.validate)) "reject missing native table offsets"
    check (rejected ({word with table_offsets := word.table_offsets.set! 24 65536}.validate))
      "reject shifted native ROM table"
    check (rejected ({c with table_offsets := c.table_offsets.set! 0 1}.validate))
      "reject invented arithmetic generic setup rows"
    check (rejected (parseCircuit "{}")) "reject missing required schema"
    let setupSource ← IO.FS.readFile "artifacts/setup/word-memory-native.json"
    let setup ← IO.ofExcept (Setup.parse setupSource)
    check (setup.tables.map (·.id) == #[0,23,24] && setup.generic_rows == 1114113)
      "actual native table-driver export geometry"
    check (setup.decoder.columns.size == 10 && setup.range16.columns.size == 1)
      "actual native decoder and scalar export widths"
    check (rejected ({setup with version := 2}.validate)) "reject unsupported setup export version"
    check (rejected ({setup with field_modulus := 2013265921}.validate)) "reject v3 setup field"
    check (rejected ({setup with family := "add_sub"}.validate)) "reject unselected setup family"
    check (rejected ({setup with generic_rows := 1114112}.validate)) "reject lost exported generic row"
    check (rejected ({setup with tables := setup.tables.extract 1 3}.validate)) "reject lost exported dummy table"
    let some rom := setup.tables[2]? | throw (IO.userError "missing exported ROM region")
    check (rejected ({setup with tables := setup.tables.set! 2 {rom with id := 34}}.validate))
      "reject v3 exported ROM tag"
    check (rejected ({setup with tables := setup.tables.set! 2 {rom with offset := 65536}}.validate))
      "reject shifted exported ROM region"
    check (rejected ({setup with tables := setup.tables.set! 2 {rom with data :=
      {rom.data with columns := rom.data.columns.extract 0 3}}}.validate)) "reject missing exported tag column"
    check (rejected ({setup with decoder := {setup.decoder with length := 1048575}}.validate))
      "reject truncated exported decoder domain"
    check (rejected ({setup with decoder := {setup.decoder with columns := setup.decoder.columns.extract 0 9}}.validate))
      "reject missing exported decoder column"
    check (rejected ({setup with range16 := {setup.range16 with columns := #[⟨#[.affine 65535 0 1]⟩]}}.validate))
      "reject incomplete compressed scalar column"
    check (rejected ((⟨#[.affine 4 2147483647 0]⟩ : Setup.Column).validate 4 mersenne31Modulus))
      "reject noncanonical compressed field value"
    check (rejected ((⟨#[.affine 4 0 (-1)]⟩ : Setup.Column).validate 4 mersenne31Modulus))
      "reject negative affine endpoint"
    check (rejected ((⟨#[.periodic 4 (-1) #[0]]⟩ : Setup.Column).validate 4 mersenne31Modulus))
      "reject negative periodic endpoint"
    check (rejected ((⟨#[.periodic 0 0 #[1]]⟩ : Setup.Column).validate 0 mersenne31Modulus))
      "reject zero-length periodic block"
    check (rejected ((⟨#[.dense #[]]⟩ : Setup.Column).validate 0 mersenne31Modulus))
      "reject empty dense block"
    check (rejected ((⟨#[.affine 1 0 9223372036854775808]⟩ : Setup.Column).validate 1 mersenne31Modulus))
      "reject out-of-Rust-range compressed stride"
    check (rejected ({setup with program := {setup.program with image_words := 4}}.validate))
      "reject unpadded exported image extent"
    check (rejected ({setup with program := {setup.program with text_words := 1048577}}.validate))
      "reject oversized exported text extent"
    let setupJson ← IO.ofExcept (Json.parse setupSource)
    let unknown ← IO.ofExcept (replaceField setupJson "invented" (.bool true))
    check (rejected (Setup.parse unknown.compress)) "reject unknown setup export field"
    let badBlock ← IO.ofExcept (Json.parse "{\"kind\":\"affine\",\"length\":1,\"first\":0,\"step\":0,\"invented\":1}")
    check (rejected (fromJson? badBlock : Except String Setup.Block)) "reject unknown compressed block field"
    scalarChecks setupSource
    decoderChecks setupSource
    controlDecoderChecks
    decoderPaddingChecks
    controlChecks
    mulDivChecks
    return (0 : UInt32)
  catch error =>
    IO.eprintln s!"FAIL {error}"
    return (1 : UInt32)
