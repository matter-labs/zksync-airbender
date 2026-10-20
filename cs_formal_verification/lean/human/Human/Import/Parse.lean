import Human.Import.Schema
import Human.Helpers.Memory.IndirectPorts
import Human.Helpers.Context.Columns
import Human.Helpers.Memory.Ports
import Human.Helpers.Delegation.Columns
import Human.Helpers.Decoder.Columns

namespace Airbender
open Lean

/-- Scratch aliases must agree in both emitted maps before resolving a lookup. -/
private def Circuit.lookupAddress (c : Circuit) (address : GKRAddress) : Except String GKRAddress := do
  match address with
  | .ScratchSpace i =>
    let some original := c.scratch_space_mapping_rev.entries.toList.lookup i
      | throw "lookup scratch alias has no reverse mapping"
    match (c.scratch_space_mapping.filter fun (_, j) => j == i).toList with
    | [(forward, _)] =>
      unless forward == original do throw "lookup scratch maps disagree"
      match original with
      | .ScratchSpace _ => throw "nested lookup scratch alias is unsupported"
      | _ => pure original
    | _ => throw "lookup scratch alias must have exactly one forward mapping"
  | _ => pure address

/-- Recover one logical variable for a physical address; reject ambiguity. -/
private def Circuit.logicalVariable (c : Circuit) (address : GKRAddress) : Except String Nat := do
  let address ← c.lookupAddress address
  let placements := c.placement_data.entries.filter fun (_, a) => a == address
  match placements.toList with
  | [(v, _)] => pure v
  | _ => throw s!"address must have exactly one logical variable: {repr address}"

/-- Recover logical variables for physical lookup addresses; reject ambiguity. -/
def Circuit.lookupExpression (c : Circuit) (relation : LinearRelation) : Except String Expr := do
    let terms ← relation.linear_terms.mapM fun (coeff, address) => do
      pure (.Product #[.Constant coeff, .Var (← c.logicalVariable address)] : Expr)
    pure (.Sum (#[.Constant relation.constant] ++ terms))

/-- Import indirect word ports, preserving optional variable offsets, order, scale and
    read/write direction. The caller guards the expected family profile. -/
def Circuit.indirectPorts (c : Circuit) : Except String (Array Verification.IndirectPort) := do
  let logicalColumns := fun (columns : Fixed 2 Nat) => do
    unless columns.values.all (· < c.memory_layout.total_width) do
      throw "indirect port column is outside memory layout"
    let lo ← c.logicalVariable (.BaseLayerMemory columns.values[0]!)
    let hi ← c.logicalVariable (.BaseLayerMemory columns.values[1]!)
    pure (#v[lo, hi] : Vector Nat 2)
  let wordColumns := fun (value : RamWordRepresentation) => do
    let .U16Limbs columns := value | throw "indirect port requires two-limb words"
    logicalColumns columns
  let mut ports := #[]
  let mut offsetColumns := #[]
  for query in c.memory_layout.ram_access_sets do
    let (address, read, write) := match query with
      | .Readonly q => (q.address, q.read_value, none)
      | .Write q => (q.address, q.read_value, some q.write_value)
    if let .IndirectRam a := address then
      let (scale, offset) ← match a.variable_offset with
        | none => pure (0, none)
        | some (scale, offset) => do
          unless offset < c.memory_layout.total_width do
            throw "indirect port column is outside memory layout"
          if !offsetColumns.contains offset then
            offsetColumns := offsetColumns.push offset
          pure (scale.val, some (← c.logicalVariable (.BaseLayerMemory offset)))
      let base ← logicalColumns a.base_register_value
      let read ← wordColumns read
      let write ← write.mapM wordColumns
      ports := ports.push ⟨a.base_register_index.val, a.indirect_access_idx_for_register,
        base, scale, offset, a.constant_offset.val, read, write⟩
  unless offsetColumns == c.memory_layout.indirect_access_variable_offsets do
    throw "indirect port offsets disagree with memory layout"
  return ports

def Circuit.range16Expressions (c : Circuit) : Except String (Array Expr) :=
  c.range_check_16_lookup_expressions.mapM fun query => c.lookupExpression query.input


def Circuit.timestampExpressions (c : Circuit) : Except String (Array Expr) :=
  c.timestamp_range_check_lookup_expressions.mapIdxM fun index query => do
    unless query.lookup_set_index == index do throw "timestamp lookup set order mismatch"
    c.lookupExpression query.input

private def Circuit.timestampPorts (c : Circuit) (expectedOffset : Nat → Nat) :
    Except String (Array Trace.TimestampPort) := do
  let column := fun n => do
    unless n < c.memory_layout.total_width do throw "trace column outside memory layout"
    c.logicalVariable (.BaseLayerMemory n)
  let pair := fun (columns : Fixed 2 Nat) => do
    pure (#v[← column columns.values[0]!, ← column columns.values[1]!] : Vector Nat 2)
  let queries := c.memory_layout.ram_access_sets
  let borrows := c.aux_layout_data.shuffle_ram_timestamp_comparison_aux_vars
  unless queries.size == borrows.size do throw "timestamp comparison count differs from memory ports"
  unless c.timestamp_range_check_lookup_expressions.size == 2 + 2 * queries.size do
    throw "timestamp query count differs from state and memory ports"
  let mut ports := #[]
  for i in [:queries.size] do
    let some query := queries[i]? | throw "memory timestamp port is missing"
    let some auxiliary := borrows[i]? | throw "memory timestamp borrow is missing"
    let (offset, previous) := match query with
      | .Readonly q => (q.in_cycle_write_index.val, q.read_timestamp)
      | .Write q => (q.in_cycle_write_index.val, q.read_timestamp)
    unless offset == expectedOffset i && offset < 4 do throw "memory timestamp offset profile mismatch"
    ports := ports.push ⟨offset, ← pair previous, ← c.logicalVariable auxiliary.intermediate_borrow⟩
  return ports

/-- Resolve native machine clocks and consecutive in-cycle port slots. -/
def Circuit.traceColumns (c : Circuit) : Except String Trace.TraceColumns := do
  let some state := c.memory_layout.machine_state | throw "trace metadata requires machine state"
  let column := fun n => do
    unless n < c.memory_layout.total_width do throw "trace column outside memory layout"
    c.logicalVariable (.BaseLayerMemory n)
  let pair := fun (columns : Fixed 2 Nat) => do
    pure (#v[← column columns.values[0]!, ← column columns.values[1]!] : Vector Nat 2)
  pure ⟨← column state.execute, ← pair state.initial_state.pc, ← pair state.final_state.pc,
    ← pair state.initial_state.timestamp, ← pair state.final_state.timestamp,
    ← c.timestampPorts id⟩

/-- Delegation ports share write slot two, as emitted by
    `gkr_compiler/delegation_mem_accesses.rs`. Preserve the actual invocation,
    previous timestamps and Boolean borrows; there is no final machine clock. -/
def Circuit.delegationColumns (c : Circuit) : Except String Delegation.ClockColumns := do
  let some state := c.memory_layout.delegation_state | throw "delegation metadata is missing"
  unless c.memory_layout.machine_state.isNone && c.memory_layout.decoder_input.isNone do
    throw "delegation metadata cannot contain machine/decoder state"
  let column := fun n => do
    unless n < c.memory_layout.total_width do throw "delegation clock outside memory layout"
    c.logicalVariable (.BaseLayerMemory n)
  pure ⟨← column state.execute,
    #v[← column state.invocation_timestamp.values[0]!, ← column state.invocation_timestamp.values[1]!],
    ← c.timestampPorts (fun _ => 2)⟩

/-- Native decoder fields use memory columns for rs1 and either memory or
    witness columns for the immediate/funct3 group, as recorded by Rust. -/
def Circuit.decoderColumns (c : Circuit) : Except String Trace.DecoderColumns := do
  let some decoder := c.memory_layout.decoder_input | throw "decoder metadata is missing"
  let memory := fun n => do
    unless n < c.memory_layout.total_width do throw "decoder memory column outside layout"
    c.logicalVariable (.BaseLayerMemory n)
  let dataColumn := fun n => do
    if decoder.decoder_witness_is_in_memory then
      memory n
    else
      unless n < c.witness_layout.total_width do throw "decoder witness column outside layout"
      c.logicalVariable (.BaseLayerWitness n)
  pure ⟨← memory decoder.rs1_index, ← c.logicalVariable decoder.rs2_index,
    ← c.logicalVariable decoder.rd_index,
    #v[← dataColumn decoder.imm.values[0]!, ← dataColumn decoder.imm.values[1]!],
    ← decoder.funct3.mapM dataColumn, ← decoder.circuit_family_mask_bits.mapM c.logicalVariable⟩

private def Circuit.resolveMemoryPorts (c : Circuit) (clocks : Array Trace.TimestampPort)
    (delegation : Bool) : Except String (Array Trace.MemoryPort) := do
  let indirects ← if delegation then c.indirectPorts else pure #[]
  let mut indirectIndex := 0
  let mut ports := #[]
  let column := fun n => do
    unless n < c.memory_layout.total_width do throw "memory port column outside layout"
    c.logicalVariable (.BaseLayerMemory n)
  let pair := fun (columns : Fixed 2 Nat) => do
    pure (#v[← column columns.values[0]!, ← column columns.values[1]!] : Vector Nat 2)
  let word := fun (value : RamWordRepresentation) => do
    match value with
    | .Zero => pure Trace.WordColumns.zero
    | .U16Limbs columns => pure (Trace.WordColumns.u16 (← pair columns))
    | .U8Limbs columns => pure (Trace.WordColumns.u8
        #v[← column columns.values[0]!, ← column columns.values[1]!,
          ← column columns.values[2]!, ← column columns.values[3]!])
  for i in [:c.memory_layout.ram_access_sets.size] do
    let some query := c.memory_layout.ram_access_sets[i]? | throw "memory port is missing"
    let (address, read, write) := match query with
      | .Readonly q => (q.address, q.read_value, none)
      | .Write q => (q.address, q.read_value, some q.write_value)
    let address ← match address with
      | .ConstantRegister index => pure (.constantRegister index.val)
      | .RegisterOnly register => do
        if delegation then throw "delegation requires fixed register addresses"
        pure (.register (← column register.register_index))
      | .RegisterOrRam mixed => do
        if delegation then throw "delegation requires distinct register/RAM spaces"
        let (selector, registerOnTrue) := match mixed.address_space with
          | .RegisterAddressSpace column => (column, true)
          | .RamAddressSpace column => (column, false)
        pure (.mixed (← column selector) registerOnTrue (← pair mixed.address))
      | .IndirectRam _ => do
        let some port := indirects[indirectIndex]?
          | throw "indirect ports are outside the direct memory profile"
        indirectIndex := indirectIndex + 1
        pure (.indirect port)
    let some clock := clocks[i]? | throw "memory port has no clock descriptor"
    ports := ports.push ⟨clock, address, ← word read, ← write.mapM word⟩
  unless indirectIndex == indirects.size do throw "indirect memory port count mismatch"
  return ports

/-- Direct register/RAM ports for ordinary instruction rows. -/
def Circuit.memoryPorts (c : Circuit) : Except String (Array Trace.MemoryPort) := do
  c.resolveMemoryPorts (← c.traceColumns).ports false

/-- Every delegation port, including fixed registers and ordered indirect RAM
    accesses, paired with its own native previous timestamp and write slot. -/
def Circuit.delegationPorts (c : Circuit) : Except String (Array Trace.MemoryPort) := do
  c.resolveMemoryPorts (← c.delegationColumns).ports true

/-- Validate a fixed-table query shape, including tags, padding and placement. -/
private def Circuit.fixedQueries (c : Circuit) (width : Nat) (tables : List (Nat × Nat)) :
    Except String (Array (Nat × Array Expr)) := do
  unless c.tables_ids_in_generic_lookups && c.generic_lookup_tables_width == width && width > 0 do
    throw "fixed lookups have an unsupported width or missing table IDs"
  c.generic_lookups.mapM fun query => do
    unless query.columns.size == width do throw "fixed lookup width mismatch"
    let some tag := query.columns[width - 1]? | throw "fixed lookup is missing its table ID"
    unless tag.linear_terms.isEmpty do throw "fixed lookup table ID must be constant"
    let id := tag.constant.canonical.val
    let some arity := tables.lookup id | throw s!"unsupported fixed table ID: {id}"
    for i in [arity:width - 1] do
      let some padding := query.columns[i]? | throw "fixed lookup is missing padding"
      unless padding.linear_terms.isEmpty && padding.constant.canonical.val == 0 do
        throw "fixed lookup padding must be zero"
    let expressions ← (query.columns.extract 0 arity).mapM c.lookupExpression
    pure (id, expressions)

def Circuit.comparisonQueries (c : Circuit) : Except String (Array (Nat × Array Expr)) :=
  c.fixedQueries 10 [(1, 2), (5, 2), (31, 2), (2, 3)]

def Circuit.mulDivQueries (c : Circuit) : Except String (Array (Nat × Array Expr)) :=
  c.fixedQueries 9 [(1, 2), (41, 2), (26, 1)]

/-- Retain the native bigint setup columns, including each fixed table tag.
    Rows are supplied separately; importing queries does not certify setup provenance. -/
def Circuit.bigintQueries (c : Circuit) : Except String (Array (Array Expr)) := do
  let _ ← c.fixedQueries 3 [(41, 2), (22, 2), (23, 2), (24, 1), (25, 1), (26, 1)]
  unless c.num_generic_lookups == 61 && c.generic_lookups.size == 61 &&
      !c.has_decoder_lookup do throw "bigint requires sixty-one fixed queries and no decoder"
  c.generic_lookups.mapIdxM fun index query => do
    unless query.lookup_set_index == index do throw "bigint lookup set order mismatch"
    query.columns.mapM c.lookupExpression

/-- Preserve all columns of variable-tag byte queries, including the tag itself.
    Validate the setup profile and the otherwise unused ninth column. -/
def Circuit.shiftBinopQueries (c : Circuit) : Except String (Array (Array Expr)) := do
  unless c.tables_ids_in_generic_lookups && c.generic_lookup_tables_width == 10 do
    throw "shift/binop lookups require ten columns and explicit table IDs"
  unless c.has_decoder_lookup && c.offset_for_decoder_table == 524545 &&
      c.total_tables_size == 1573121 do throw "unexpected shift/binop setup/decoder boundary"
  unless c.table_offsets.size > 9 do throw "shift/binop table offsets are incomplete"
  for id in [:c.table_offsets.size] do
    let offset := if id == 0 then 0 else if id ≤ 3 then 1 else if id == 4 then 257
      else if id ≤ 6 then 65793 else if id == 7 then 131329 else if id == 8 then 196865
      else if id == 9 then 262401 else 524545
    unless (c.table_offsets[id]?.map (·.val)) == some offset do
      throw "unexpected shift/binop table offset"
  unless c.num_generic_lookups == 6 && c.generic_lookups.size == 5 do
    throw "shift/binop requires five byte-query sets plus the decoder set"
  c.generic_lookups.toList.zipIdx.toArray.mapM fun (query, index) => do
    unless query.columns.size == 10 && query.lookup_set_index == index do
      throw "unsupported shift/binop query width or set"
    let some padding := query.columns[8]? | throw "shift/binop query is missing padding"
    unless padding.linear_terms.isEmpty && padding.constant.canonical.val == 0 do
      throw "shift/binop lookup padding must be zero"
    query.columns.mapM c.lookupExpression

/-- Preserve the conditional ROM query; its program-dependent table is supplied
    by the caller. Check the standard word-memory setup profile and zero padding. -/
def Circuit.wordMemoryQueries (c : Circuit) : Except String (Array (Array Expr)) := do
  unless c.tables_ids_in_generic_lookups && c.generic_lookup_tables_width == 9 do
    throw "word-memory lookups require nine columns and explicit table IDs"
  unless c.has_decoder_lookup && c.offset_for_decoder_table == 1048577 &&
      c.total_tables_size == 2097153 do throw "unexpected word-memory setup/decoder boundary"
  unless c.table_offsets.size > 34 do throw "word-memory table offsets are incomplete"
  for id in [:c.table_offsets.size] do
    let offset := if id == 0 then 0 else if id ≤ 34 then 1 else 1048577
    unless (c.table_offsets[id]?.map (·.val)) == some offset do
      throw "unexpected word-memory table offset"
  unless c.num_generic_lookups == 2 && c.generic_lookups.size == 1 do
    throw "word-memory requires one ROM-query set plus the decoder set"
  c.generic_lookups.mapM fun query => do
    unless query.columns.size == 9 && query.lookup_set_index == 0 do
      throw "unsupported word-memory query width or set"
    for i in [3:8] do
      let some padding := query.columns[i]? | throw "word-memory query is missing padding"
      unless padding.linear_terms.isEmpty && padding.constant.canonical.val == 0 do
        throw "word-memory lookup padding must be zero"
    query.columns.mapM c.lookupExpression

/-- Subword memory uses the same tagged setup table for both query sets:
    fixed byte clearing, then the conditional contribution/ROM query. -/
def Circuit.subwordMemoryQueries (c : Circuit) : Except String (Array (Array Expr)) := do
  unless c.tables_ids_in_generic_lookups && c.generic_lookup_tables_width == 9 do
    throw "subword-memory lookups require nine columns and explicit table IDs"
  unless c.has_decoder_lookup && c.offset_for_decoder_table == 13238273 &&
      c.total_tables_size == 14286849 do throw "unexpected subword-memory setup/decoder boundary"
  unless c.table_offsets.size > 46 do throw "subword-memory table offsets are incomplete"
  for id in [:c.table_offsets.size] do
    let offset := if id == 0 then 0 else if id < 30 then 1 else if id < 31 then 131073
      else if id < 43 then 262145 else if id < 44 then 393217 else if id < 45 then 655361
      else if id < 46 then 4849665 else 13238273
    unless (c.table_offsets[id]?.map (·.val)) == some offset do
      throw "unexpected subword-memory table offset"
  unless c.num_generic_lookups == 3 && c.generic_lookups.size == 2 do
    throw "subword-memory requires two query sets plus the decoder set"
  c.generic_lookups.mapIdxM fun index query => do
    unless query.columns.size == 9 && query.lookup_set_index == index do
      throw "unsupported subword-memory query width or set"
    let paddingStart := if index == 0 then 2 else 3
    for i in [paddingStart:8] do
      let some padding := query.columns[i]? | throw "subword-memory query is missing padding"
      unless padding.linear_terms.isEmpty && padding.constant.canonical.val == 0 do
        throw "subword-memory lookup padding must be zero"
    if index == 0 then
      let some tag := query.columns[8]? | throw "subword-memory query is missing its table ID"
      unless tag.linear_terms.isEmpty && tag.constant.canonical.val == 30 do
        throw "subword-memory clearing query requires table ID 30"
    query.columns.mapM c.lookupExpression

/-- The unified machine pools five variable-tag queries. Preserve every data
    column and validate the fixed setup profile and common zero padding. -/
def Circuit.unifiedReducedQueries (c : Circuit) : Except String (Array (Array Expr)) := do
  unless c.tables_ids_in_generic_lookups && c.generic_lookup_tables_width == 10 do
    throw "unified reduced lookups require ten columns and explicit table IDs"
  unless c.has_decoder_lookup && c.offset_for_decoder_table == 2097537 &&
      c.total_tables_size == 3146113 do throw "unexpected unified reduced setup/decoder boundary"
  let offsets : Array Nat := #[
    0, 1, 131073, 196609, 196865, 196865, 262401, 262401, 262401, 327937,
    590081, 590081, 590081, 590081, 590081, 590081, 590081, 590081, 590081, 590081,
    590081, 590081, 590081, 590081, 590081, 590081, 590081, 590081, 590081, 590081,
    590081, 590081, 590081, 590081, 590081, 1638657, 1638657, 1638657, 1638657, 1638657,
    1638657, 1638657, 1638657, 1638657, 1638657, 1638657, 1638657, 1638657, 1704193, 1769729,
    1835265, 1900801, 1900929, 1966465, 2032001]
  unless c.table_offsets.size == offsets.size do throw "unified reduced table offsets are incomplete"
  for id in [:offsets.size] do
    unless (c.table_offsets[id]?.map (·.val)) == offsets[id]? do
      throw "unexpected unified reduced table offset"
  unless c.num_generic_lookups == 6 && c.generic_lookups.size == 5 do
    throw "unified reduced requires five pooled-query sets plus the decoder set"
  c.generic_lookups.mapIdxM fun index query => do
    unless query.columns.size == 10 && query.lookup_set_index == index do
      throw "unsupported unified reduced query width or set"
    let some padding := query.columns[8]? | throw "unified reduced query is missing padding"
    unless padding.linear_terms.isEmpty && padding.constant.canonical.val == 0 do
      throw "unified reduced query padding must be zero"
    query.columns.mapM c.lookupExpression

/-- BLAKE2s G has one eight-data-column control query and eighteen three-data-column
    XOR queries. Keep the control columns, chunk widths/tags and query order intact. -/
def Circuit.blakeGQueries (c : Circuit) : Except String (Array (Array Expr)) := do
  unless c.tables_ids_in_generic_lookups && c.generic_lookup_tables_width == 9 do
    throw "BLAKE2 G lookups require nine columns and explicit table IDs"
  unless !c.has_decoder_lookup && c.offset_for_decoder_table == 344896 &&
      c.total_tables_size == 344896 do throw "unexpected BLAKE2 G setup boundary"
  let offsets : Array Nat := #[
    0, 0, 0, 0, 0, 65536, 65536, 65536, 65536, 65536,
    65536, 65536, 65536, 65536, 65536, 65536, 65536, 65536, 65600, 65856,
    82240, 344384, 344384, 344384, 344384, 344384, 344384, 344384, 344384, 344896,
    344896, 344896, 344896, 344896, 344896, 344896, 344896, 344896, 344896, 344896,
    344896, 344896, 344896, 344896, 344896, 344896, 344896, 344896, 344896, 344896,
    344896, 344896, 344896, 344896, 344896]
  unless c.table_offsets.size == offsets.size do throw "BLAKE2 G table offsets are incomplete"
  for id in [:offsets.size] do
    unless (c.table_offsets[id]?.map (·.val)) == offsets[id]? do
      throw "unexpected BLAKE2 G table offset"
  let tags := #[28, 4, 4, 4, 4, 17, 20, 18, 17, 20, 18, 4, 4, 4, 4, 19, 20, 19, 20]
  unless c.num_generic_lookups == tags.size && c.generic_lookups.size == tags.size do
    throw "BLAKE2 G requires one control query and eighteen XOR queries"
  c.generic_lookups.mapIdxM fun index query => do
    unless query.columns.size == 9 && query.lookup_set_index == index do
      throw "unsupported BLAKE2 G query width or set"
    let some tag := query.columns[8]? | throw "BLAKE2 G query is missing its table ID"
    unless tag.linear_terms.isEmpty && some tag.constant.canonical.val == tags[index]? do
      throw "unexpected BLAKE2 G table ID"
    if index != 0 then
      for i in [3:8] do
        let some padding := query.columns[i]? | throw "BLAKE2 G query is missing padding"
        unless padding.linear_terms.isEmpty && padding.constant.canonical.val == 0 do
          throw "BLAKE2 G XOR lookup padding must be zero"
    query.columns.mapM c.lookupExpression

/-- The extended-control round has eight G invocations and final XOR queries.
    Its setup is exactly the five XOR regions, with three data columns and a tag. -/
def Circuit.blakeRoundQueries (c : Circuit) : Except String (Array (Array Expr)) := do
  unless c.tables_ids_in_generic_lookups && c.generic_lookup_tables_width == 4 do
    throw "BLAKE2 round lookups require four columns and explicit table IDs"
  unless !c.has_decoder_lookup && c.offset_for_decoder_table == 344384 &&
      c.total_tables_size == 344384 do throw "unexpected BLAKE2 round setup boundary"
  let offsets := #[0, 0, 0, 0, 0, 65536, 65536, 65536, 65536, 65536,
    65536, 65536, 65536, 65536, 65536, 65536, 65536, 65536, 65600, 65856, 82240] ++
    Array.replicate 34 344384
  unless c.table_offsets.size == offsets.size do throw "BLAKE2 round table offsets are incomplete"
  for id in [:offsets.size] do
    unless (c.table_offsets[id]?.map (·.val)) == offsets[id]? do
      throw "unexpected BLAKE2 round table offset"
  let gTags := [4, 4, 4, 4, 17, 20, 18, 17, 20, 18, 4, 4, 4, 4, 19, 20, 19, 20]
  let tags := ((List.replicate 8 gTags).flatten ++
    (List.replicate 16 [19, 20]).flatten ++ (List.replicate 8 [20, 19, 4, 4]).flatten).toArray
  unless c.num_generic_lookups == tags.size && c.generic_lookups.size == tags.size do
    throw "BLAKE2 round requires 208 XOR queries"
  c.generic_lookups.mapIdxM fun index query => do
    unless query.columns.size == 4 && query.lookup_set_index == index do
      throw "unsupported BLAKE2 round query width or set"
    let some tag := query.columns[3]? | throw "BLAKE2 round query is missing its table ID"
    unless tag.linear_terms.isEmpty && some tag.constant.canonical.val == tags[index]? do
      throw "unexpected BLAKE2 round table ID"
    query.columns.mapM c.lookupExpression

/-- Six-index control query followed by forty variable-tag byte operations.
    Preserve all tag expressions; validate the setup profile and unused padding. -/
def Circuit.keccakQueries (c : Circuit) : Except String (Array (Array Expr)) := do
  unless c.tables_ids_in_generic_lookups && c.generic_lookup_tables_width == 8 do
    throw "Keccak lookups require eight columns and explicit table IDs"
  unless !c.has_decoder_lookup && c.offset_for_decoder_table == 1249281 &&
      c.total_tables_size == 1249281 do throw "unexpected Keccak setup boundary"
  let offsets := #[0] ++ Array.replicate 4 1 ++ Array.replicate 33 65537 ++
    #[69633, 135169, 200705] ++ Array.replicate 14 1249281
  unless c.table_offsets.size == offsets.size do throw "Keccak table offsets are incomplete"
  for id in [:offsets.size] do
    unless (c.table_offsets[id]?.map (·.val)) == offsets[id]? do
      throw "unexpected Keccak table offset"
  unless c.num_generic_lookups == 41 && c.generic_lookups.size == 41 do
    throw "Keccak requires one control query and forty byte queries"
  c.generic_lookups.mapIdxM fun index query => do
    unless query.columns.size == 8 && query.lookup_set_index == index do
      throw "unsupported Keccak query width or set"
    if index == 0 then
      let some tag := query.columns[7]? | throw "Keccak control query is missing its table ID"
      unless tag.linear_terms.isEmpty && tag.constant.canonical.val == 37 do
        throw "Keccak control query requires table ID 37"
    else
      for i in [3:7] do
        let some padding := query.columns[i]? | throw "Keccak byte query is missing padding"
        unless padding.linear_terms.isEmpty && padding.constant.canonical.val == 0 do
          throw "Keccak byte lookup padding must be zero"
    query.columns.mapM c.lookupExpression

/-- Decode the Rust artifact using Lean's JSON parser and the typed serde mirror. -/
def parseCircuit (text : String) : Except String Circuit := do
  fromJson? (← Json.parse text)

def loadCircuit (path : System.FilePath) : IO (Except String Circuit) := do
  return parseCircuit (← IO.FS.readFile path)

end Airbender
