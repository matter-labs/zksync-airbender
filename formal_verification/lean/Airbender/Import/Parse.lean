import Airbender.Import.Schema
import Airbender.Review.Helpers.Memory.Ports
import Airbender.Review.Helpers.Decoder.Columns
import Airbender.Review.Helpers.Tables.SetupColumns

namespace Airbender
open Lean

def Circuit.logicalVariable (c : Circuit) (address : ColumnAddress) : Except String Nat := do
  let inBounds : Bool := match address with
    | .WitnessSubtree n => decide (n < c.witness_layout.total_width)
    | .MemorySubtree n => decide (n < c.memory_layout.total_width)
    | .SetupSubtree n => decide (n < c.setup_layout.total_width)
  unless inBounds do throw "physical column outside native layout"
  match (c.variable_mapping.entries.filter fun (_, a) => a == address).toList with
  | [(v, _)] => pure v
  | _ => throw "physical column must have exactly one logical variable"

def Circuit.linearExpression (c : Circuit) (relation : CompiledDegree1Constraint) :
    Except String Expr := do
  let terms ← relation.linear_terms.mapM fun (a, v) => do
    pure (.Product #[.Constant a, .Var (← c.logicalVariable v)] : Expr)
  pure (.Sum (#[.Constant relation.constant_term] ++ terms))

def Circuit.quadraticExpression (c : Circuit) (relation : CompiledDegree2Constraint) :
    Except String Expr := do
  let terms ← relation.quadratic_terms.mapM fun t => do
    pure (.Product #[.Constant t.first, .Var (← c.logicalVariable t.second),
      .Var (← c.logicalVariable t.third)] : Expr)
  let linear ← c.linearExpression ⟨relation.linear_terms, relation.constant_term⟩
  pure (.Sum (#[linear] ++ terms))

def Circuit.lookupExpression (c : Circuit) : LookupExpression → Except String Expr
  | .Variable a => Expr.Var <$> c.logicalVariable a
  | .Expression e => c.linearExpression e

private def Circuit.hasBoolean (c : Circuit) (address : ColumnAddress) : Bool :=
  c.degree_2_constraints.any fun q =>
    match q.quadratic_terms.toList, q.linear_terms.toList with
    | [term], [(coefficient, column)] =>
      term.first.canonical == 1 && term.second == address && term.third == address &&
        coefficient.canonical == mersenne31Modulus - 1 && column == address &&
        q.constant_term.canonical == 0
    | _, _ => false

/-- Validate the selected v2 physical setup geometry, including full table
    offsets and the row reserved by get_main_domain_trace/normalization.
    This imports placement, not Rust-generated field values or LDE commitments. -/
def Circuit.setupColumns (c : Circuit) : Except String Verification.SetupColumns := do
  let layout := c.setup_layout
  unless c.trace_len == 16777216 && c.executor_family_decoder_table_size == 1048576 do
    throw "unsupported native setup trace/decoder capacity"
  unless layout.timestamp_setup_columns.num_elements == 0 do
    throw "native timestamp setup groups are not supported"
  unless layout.range_check_16_setup_column.start == 0 &&
      layout.range_check_16_setup_column.num_elements == 1 &&
      layout.timestamp_range_check_setup_column.start == 1 &&
      layout.timestamp_range_check_setup_column.num_elements == 1 do
    throw "unsupported native scalar setup placement"
  let generic := if c.witness_layout.width_3_lookups.isEmpty then 0 else 1
  let rows := if generic == 0 then 0 else 1114113
  unless layout.generic_lookup_setup_columns.start == 2 &&
      layout.generic_lookup_setup_columns.num_elements == generic do
    throw "unsupported native tagged setup groups"
  unless layout.preprocessed_decoder_setup_columns.start == 2 + 4 * generic &&
      layout.preprocessed_decoder_setup_columns.num_elements == 1 &&
      layout.total_width == 12 + 4 * generic do
    throw "overlapping or incomplete native decoder setup placement"
  unless c.total_tables_size == rows && c.table_offsets.size == 62 do
    throw "unsupported native generic setup extent"
  let expected := (List.range 62).toArray.map fun id =>
    if generic == 0 || id == 0 then 0 else if id ≤ 23 then 1 else if id == 24 then 65537 else 1114113
  unless c.table_offsets == expected do
    throw "unsupported native fixed-table offsets"
  pure ⟨c.trace_len, layout.total_width, 0, 1, 2, generic,
    layout.preprocessed_decoder_setup_columns.start, c.executor_family_decoder_table_size, rows⟩

/-- Check every consumed address and expression before emitting a theorem target. -/
def Circuit.validate (c : Circuit) : Except String Unit := do
  let _ ← c.setupColumns
  let keys := c.variable_mapping.entries.map Prod.fst
  unless keys.toList.Nodup do throw "duplicate logical variable IDs"
  for (_, address) in c.variable_mapping.entries do
    let _ ← c.logicalVariable address
  let w := c.witness_layout
  unless w.boolean_vars_columns_range.start + w.boolean_vars_columns_range.num_elements ≤ w.total_width do
    throw "Boolean column range outside witness layout"
  unless w.range_check_8_columns.num_elements == 0 do
    throw "8-bit range columns are not yet supported"
  unless w.range_check_16_columns.start + w.range_check_16_columns.num_elements ≤ w.total_width do
    throw "16-bit column range outside witness layout"
  for i in [:w.boolean_vars_columns_range.num_elements] do
    unless c.hasBoolean (.WitnessSubtree (w.boolean_vars_columns_range.start + i)) do
      throw "native Boolean column lacks its polynomial constraint"
  for i in [:w.range_check_16_columns.num_elements] do
    let address := ColumnAddress.WitnessSubtree (w.range_check_16_columns.start + i)
    unless w.range_check_16_lookup_expressions.any (fun query => match query with
        | .Variable a => a == address
        | _ => false) do
      throw "native 16-bit column lacks its range query"
  for q in c.degree_2_constraints do
    let _ ← c.quadraticExpression q
  for q in c.degree_1_constraints do
    let _ ← c.linearExpression q
  for q in w.width_3_lookups do
    unless q.input_columns.size == 3 do
      throw "native fixed lookup must have exactly three columns"
    for entry in q.input_columns do
      let _ ← c.lookupExpression entry
  for q in w.range_check_16_lookup_expressions ++ w.timestamp_range_check_lookup_expressions do
    let _ ← c.lookupExpression q

/-- Width is the Rust ColumnSet type parameter, not num_elements itself. -/
def Circuit.memoryColumns (c : Circuit) (columns : ColumnSet) (width : Nat) :
    Except String (Array Nat) := do
  unless columns.num_elements == 1 && columns.start + width ≤ c.memory_layout.total_width do
    throw "native memory column group has wrong extent or width"
  (List.range width).toArray.mapM fun offset =>
    c.logicalVariable (.MemorySubtree (columns.start + offset))

private def Circuit.memoryPair (c : Circuit) (columns : ColumnSet) :
    Except String (Vector Nat 2) := do
  let values ← c.memoryColumns columns 2
  pure #v[values[0]!, values[1]!]

def Circuit.traceColumns (c : Circuit) : Except String Trace.TraceColumns := do
  let some initial := c.memory_layout.intermediate_state_layout
    | throw "native initial machine state is missing"
  let some final := c.memory_layout.machine_state_layout
    | throw "native final machine state is missing"
  let queries := c.memory_layout.shuffle_ram_access_sets
  let borrows := c.memory_queries_timestamp_comparison_aux_vars
  unless queries.size == borrows.size &&
      c.witness_layout.timestamp_range_check_lookup_expressions.size == 2 + 2 * queries.size do
    throw "native timestamp queries, ports and borrows disagree"
  let ports ← queries.mapIdxM fun index query => do
    let q := match query with
      | .Readonly q => q
      | .Write q => q.toShuffleRamQueryReadColumns
    unless q.in_cycle_write_index.val == index && index < 4 do
      throw "native port offsets must be consecutive and below four"
    let some borrow := borrows[index]? | throw "native timestamp borrow is missing"
    pure (⟨index, ← c.memoryPair q.read_timestamp, ← c.logicalVariable borrow⟩ : Trace.TimestampPort)
  let active ← c.memoryColumns initial.execute 1
  pure ⟨active[0]!, ← c.memoryPair initial.pc, ← c.memoryPair final.pc,
    ← c.memoryPair initial.timestamp, ← c.memoryPair final.timestamp, ports⟩

def Circuit.memoryPorts (c : Circuit) : Except String (Array Trace.MemoryPort) := do
  let clocks ← c.traceColumns
  c.memory_layout.shuffle_ram_access_sets.mapIdxM fun index query => do
    let (q, write) := match query with
      | .Readonly q => (q, none)
      | .Write q => (q.toShuffleRamQueryReadColumns, some q.write_value)
    let address ← match q.address with
      | .RegisterOnly q => do
        let columns ← c.memoryColumns q.register_index 1
        pure (.register columns[0]! : Trace.MemoryAddress)
      | .RegisterOrRam q => do
        let selector ← c.memoryColumns q.is_register 1
        pure (.mixed selector[0]! true (← c.memoryPair q.address))
    let read := Trace.WordColumns.u16 (← c.memoryPair q.read_value)
    let write ← write.mapM fun columns => Trace.WordColumns.u16 <$> c.memoryPair columns
    let some clock := clocks.ports[index]? | throw "native port clock is missing"
    pure ⟨clock, address, read, write⟩

/-- Decoder payload groups live in the native bank selected by the state layout. -/
private def Circuit.decoderBankColumns (c : Circuit) (inMemory : Bool)
    (columns : ColumnSet) (width : Nat) : Except String (Array Nat) := do
  if inMemory then c.memoryColumns columns width
  else
    unless columns.num_elements == 1 && columns.start + width ≤ c.witness_layout.total_width do
      throw "native decoder column group has wrong extent or width"
    (List.range width).toArray.mapM fun offset =>
      c.logicalVariable (.WitnessSubtree (columns.start + offset))

/-- Resolve v2's native ten-column decoder query, keeping rd_is_zero distinct
    from the packed family mask. Extra descriptor fields fail closed for now. -/
def Circuit.decoderColumns (c : Circuit) : Except String Trace.DecoderColumns := do
  let some state := c.memory_layout.intermediate_state_layout
    | throw "native decoder state is missing"
  unless state.funct7.num_elements == 0 && state.circuit_family.num_elements == 0 do
    throw "unsupported extra native decoder fields"
  let rs1 ← c.memoryColumns state.rs1_index 1
  let zero ← c.decoderBankColumns state.decoder_witness_is_in_memory state.rd_is_zero 1
  let immediate ← c.decoderBankColumns state.decoder_witness_is_in_memory state.imm 2
  let funct3 ← c.decoderBankColumns state.decoder_witness_is_in_memory state.funct3 1
  pure ⟨rs1[0]!, ← c.logicalVariable state.rs2_index, ← c.logicalVariable state.rd_index,
    zero[0]!, #v[immediate[0]!, immediate[1]!], funct3[0]!,
    ← c.logicalVariable state.circuit_family_extra_mask⟩

def parseCircuit (source : String) : Except String Circuit := do
  let json ← Json.parse source
  let c : Circuit ← fromJson? json
  c.validate
  if c.memory_layout.intermediate_state_layout.isSome || c.memory_layout.machine_state_layout.isSome then
    let _ ← c.memoryPorts
    let _ ← c.decoderColumns
  pure c

def loadCircuit (path : System.FilePath) : IO (Except String Circuit) :=
  parseCircuit <$> IO.FS.readFile path

end Airbender
