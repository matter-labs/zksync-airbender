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
    | .OptimizedOut _ => false
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

/-- The four actual dynamic selectors of the native shift/binop artifact. -/
def Circuit.hasShiftLookups (c : Circuit) : Bool :=
  c.witness_layout.width_3_lookups.map (·.table_index) ==
    #[.Variable (.WitnessSubtree 24), .Variable (.WitnessSubtree 28),
      .Variable (.WitnessSubtree 32), .Variable (.WitnessSubtree 36)]

/-- The actual constant queries followed by two multiplexed subword slots. -/
def Circuit.hasSubwordLookups (c : Circuit) : Bool :=
  c.witness_layout.width_3_lookups.map (·.table_index) ==
    #[.Constant .MemoryGetOffsetAndMaskWithTrap, .Constant .RomAddressSpaceSeparator,
      .Variable (.WitnessSubtree 28), .Variable (.WitnessSubtree 32)]

/-- Exact six-slot reduced-machine intake profile. This does not authorize
    Clean lookup emission or establish native table contents. -/
def Circuit.hasReducedLookups (c : Circuit) : Bool :=
  c.witness_layout.width_3_lookups.map (·.table_index) ==
    #[.Constant .U16GetSignAndHighByte, .Constant .U16GetSignAndHighByte,
      .Variable (.WitnessSubtree 58), .Variable (.WitnessSubtree 62),
      .Variable (.WitnessSubtree 66), .Variable (.WitnessSubtree 70)]

/-- Validate the selected v2 physical setup geometry, including full table
    offsets and the row reserved by get_main_domain_trace/normalization.
    This imports placement, not Rust-generated field values or LDE commitments. -/
def Circuit.setupColumns (c : Circuit) : Except String Verification.SetupColumns := do
  let layout := c.setup_layout
  let reduced := c.hasReducedLookups
  unless c.trace_len == (if reduced then 8388608 else 16777216) &&
      c.executor_family_decoder_table_size == 1048576 do
    throw "unsupported native setup trace/decoder capacity"
  unless layout.timestamp_setup_columns.num_elements == 0 do
    throw "native timestamp setup groups are not supported"
  unless layout.range_check_16_setup_column.start == 0 &&
      layout.range_check_16_setup_column.num_elements == 1 &&
      layout.timestamp_range_check_setup_column.start == 1 &&
      layout.timestamp_range_check_setup_column.num_elements == 1 do
    throw "unsupported native scalar setup placement"
  let ids := c.witness_layout.width_3_lookups.map fun query =>
    match query.table_index with | .Constant id => some id | .Variable _ => none
  let memory := ids == #[some FixedTableId.RomAddressSpaceSeparator, some .RomRead]
  let control := ids == #[some FixedTableId.ConditionalJmpBranchSlt, some .JumpCleanupOffset]
  let small := !ids.isEmpty && ids.all (· == some FixedTableId.RangeCheckSmall)
  let shift := c.hasShiftLookups
  let subword := c.hasSubwordLookups
  unless ids.isEmpty || memory || control || small || shift || subword || reduced do throw "unsupported native fixed lookup profile"
  let generic := if ids.isEmpty then 0 else 1
  let regeneratedReduced := reduced && c.total_tables_size == 5771521
  let rows := if memory then 1114113 else if control then 65664 else if small then 65536 else if shift then 10817537 else if subword then 9502721 else if reduced then (if regeneratedReduced then 5771521 else 5705985) else 0
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
    if memory then
      if id == 0 then 0 else if id ≤ 23 then 1 else if id == 24 then 65537 else 1114113
    else if reduced then
      if id == 0 then 0 else if id ≤ 4 then 1 else if id ≤ 6 then 65537
      else if id == 7 then 131073 else if id ≤ 16 then 196609
      else if id == 17 then 262145 else if id == 18 then 327681
      else if id ≤ 20 then 393217 else if id ≤ 22 then 393345
      else if id == 23 then 393473 else if id == 24 then 459009
      else if id == 25 then 1507585 else if id ≤ 37 then 1511681
      else if regeneratedReduced && id > 47 then 5771521 else 5705985
    else if subword then
      if id == 0 then 0 else if id ≤ 23 then 1 else if id ≤ 44 then 65537
      else if id == 45 then 2162689 else if id == 46 then 4259841
      else if id ≤ 54 then 5308417 else if id == 55 then 7405569 else 9502721
    else if control then
      if id ≤ 17 then 0 else if id ≤ 43 then 65536 else 65664
    else if small then
      if id ≤ 8 then 0 else 65536
    else if shift then
      if id == 0 then 0 else if id ≤ 4 then 1 else if id ≤ 6 then 65537
      else if id == 7 then 131073 else if id ≤ 25 then 196609
      else if id ≤ 47 then 200705 else if id == 48 then 266241
      else if id == 49 then 2363393 else if id == 50 then 4460545
      else if id == 51 then 6557697 else if id == 52 then 8654849
      else if id == 53 then 10752001 else 10817537
    else 0
  unless c.table_offsets == expected do
    throw "unsupported native fixed-table offsets"
  pure ⟨c.trace_len, layout.total_width, 0, 1, 2, generic,
    layout.preprocessed_decoder_setup_columns.start, c.executor_family_decoder_table_size, rows⟩

/-- Check every consumed address and expression before emitting a theorem target. -/
private def Circuit.validateLocal (c : Circuit) : Except String Unit := do
  let _ ← c.setupColumns
  let keys := c.variable_mapping.entries.map Prod.fst
  unless keys.toList.Nodup do throw "duplicate logical variable IDs"
  for (_, address) in c.variable_mapping.entries do
    match address with
    | .OptimizedOut index =>
      unless index < c.scratch_space_size_for_witness_gen do
        throw "optimized-out variable outside native scratch space"
      unless (c.variable_mapping.entries.filter fun (_, a) => a == address).size == 1 do
        throw "ambiguous optimized-out scratch mapping"
    | _ => let _ ← c.logicalVariable address
  unless c.memory_layout.delegation_processor_layout.isNone do
    throw "unsupported native delegation processor layout"
  let _ ← c.stage_2_layout.raw.getObj?
  let batched := c.batched_memory_access_timestamp_comparison_aux_vars
  let indirect := c.register_and_indirect_access_timestamp_comparison_aux_vars
  unless batched.predicate == .OptimizedOut 0 &&
      batched.write_timestamp_columns.start == 0 && batched.write_timestamp_columns.num_elements == 0 &&
      batched.write_timestamp == #[.OptimizedOut 0,.OptimizedOut 0] &&
      indirect.predicate == .OptimizedOut 0 &&
      indirect.write_timestamp_columns.start == 0 && indirect.write_timestamp_columns.num_elements == 0 &&
      indirect.write_timestamp == #[.OptimizedOut 0,.OptimizedOut 0] do
    throw "unsupported active batched/indirect timestamp metadata"
  unless c.hasReducedLookups || c.memory_layout.shuffle_ram_inits_and_teardowns.isEmpty do
    throw "native initialization metadata requires the reduced intake profile"
  unless c.hasReducedLookups || c.lazy_init_address_aux_vars.isEmpty do
    throw "native initialization auxiliaries require the reduced intake profile"
  let w := c.witness_layout
  unless w.boolean_vars_columns_range.start + w.boolean_vars_columns_range.num_elements ≤ w.total_width do
    throw "Boolean column range outside witness layout"
  let bytes := w.range_check_8_columns
  unless bytes.start + bytes.num_elements ≤ w.total_width do
    throw "8-bit column range outside witness layout"
  let byteQueries := w.width_3_lookups.filter fun q =>
    match q.table_index with | .Constant id => id == .RangeCheckSmall | .Variable _ => false
  unless byteQueries.size == (bytes.num_elements + 1) / 2 do
    throw "native byte columns lack their paired fixed queries"
  let isZero := fun entry => match entry with
    | LookupExpression.Expression e => e.linear_terms.isEmpty && e.constant_term.canonical == 0
    | _ => false
  for j in [:byteQueries.size] do
    let some q := byteQueries[j]? | throw "missing native byte query"
    unless q.input_columns.size == 3 do throw "native byte lookup must have three columns"
    let some first := q.input_columns[0]? | throw "missing first native byte"
    let some second := q.input_columns[1]? | throw "missing second native byte"
    let some padding := q.input_columns[2]? | throw "missing native byte padding"
    let atColumn := fun (entry : LookupExpression) (offset : Nat) => match entry with
      | LookupExpression.Variable address => address == .WitnessSubtree (bytes.start + offset)
      | _ => false
    unless atColumn first (2 * j) &&
        (if 2 * j + 1 < bytes.num_elements then atColumn second (2 * j + 1)
         else isZero second) && isZero padding do
      throw "native byte queries do not match paired column order and zero padding"
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
    match q.table_index with
    | .Constant _ => pure ()
    | .Variable address => let _ ← c.logicalVariable address
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

/-- Native request observables. An absent ABI group stays absent; it is not
    resolved as memory column zero or interpreted as an ABI value. -/
structure DelegationRequestCoordinates where
  multiplicity : Nat
  kind : Nat
  offsetHigh : Option Nat
  clockOffset : Nat
  deriving Repr, DecidableEq

def Circuit.requestColumns (c : Circuit) : Except String (Option DelegationRequestCoordinates) := do
  if !c.hasReducedLookups && !c.hasShiftLookups then
    unless c.memory_layout.delegation_request_layout.isNone do
      throw "native delegation requests require a supported request profile"
    return none
  let some request := c.memory_layout.delegation_request_layout
    | throw "native request profile lacks its request descriptor"
  let groupAt := fun (columns : ColumnSet) (start count : Nat) =>
    columns.start == start && columns.num_elements == count
  let reduced := c.hasReducedLookups
  unless groupAt request.multiplicity (if reduced then 27 else 17) 1 &&
      groupAt request.delegation_type (if reduced then 28 else 18) 1 &&
      groupAt request.abi_mem_offset_high (if reduced then 29 else 0) (if reduced then 1 else 0) &&
      request.in_cycle_write_index.val == 3 do
    throw "unsupported native request placement or issue offset"
  let multiplicity ← c.memoryColumns request.multiplicity 1
  let kind ← c.memoryColumns request.delegation_type 1
  let offset ← if reduced then do
      let columns ← c.memoryColumns request.abi_mem_offset_high 1
      pure (some columns[0]!)
    else pure none
  pure (some ⟨multiplicity[0]!,kind[0]!,offset,3⟩)

/-- Logical coordinates of the native reduced argument descriptors. These
    are observables, not initialized-history, issue or public-value premises. -/
structure ReducedArgumentColumns where
  initialAddress : Vector Nat 2
  terminalValue : Vector Nat 2
  terminalTime : Vector Nat 2
  addressAux : Vector Nat 2
  addressBorrows : Vector Nat 2
  requestMultiplicity : Nat
  requestType : Nat
  requestOffsetHigh : Nat
  requestClockOffset : Nat
  deriving Repr, DecidableEq

def Circuit.reducedArgumentColumns (c : Circuit) : Except String ReducedArgumentColumns := do
  unless c.hasReducedLookups do throw "not the native reduced intake profile"
  let [initial] := c.memory_layout.shuffle_ram_inits_and_teardowns.toList
    | throw "reduced intake requires one native init/teardown descriptor"
  let [aux] := c.lazy_init_address_aux_vars.toList
    | throw "reduced intake requires one native initialization auxiliary"
  let some request := c.memory_layout.delegation_request_layout
    | throw "reduced intake requires native delegation request metadata"
  let groupAt := fun (columns : ColumnSet) (start : Nat) =>
    columns.start == start && columns.num_elements == 1
  unless groupAt initial.lazy_init_addresses_columns 0 &&
      groupAt initial.lazy_teardown_values_columns 2 &&
      groupAt initial.lazy_teardown_timestamps_columns 4 &&
      groupAt request.multiplicity 27 && groupAt request.delegation_type 28 &&
      groupAt request.abi_mem_offset_high 29 do
    throw "unsupported native reduced initialization/request placement"
  unless aux.aux_low_high == #[.WitnessSubtree 17,.WitnessSubtree 18] &&
      aux.intermediate_borrow == .WitnessSubtree 44 && aux.final_borrow == .WitnessSubtree 45 do
    throw "unsupported native reduced initialization auxiliary placement"
  unless request.in_cycle_write_index.val == 3 do
    throw "reduced delegation issue offset must be three"
  let address ← c.memoryPair initial.lazy_init_addresses_columns
  let value ← c.memoryPair initial.lazy_teardown_values_columns
  let time ← c.memoryPair initial.lazy_teardown_timestamps_columns
  let [low,high] := aux.aux_low_high.toList
    | throw "native initialization auxiliary must have two limbs"
  let limbs := #v[← c.logicalVariable low, ← c.logicalVariable high]
  let borrowLow ← c.logicalVariable aux.intermediate_borrow
  let borrowHigh ← c.logicalVariable aux.final_borrow
  unless c.hasBoolean aux.intermediate_borrow && c.hasBoolean aux.final_borrow do
    throw "native initialization borrow lacks its Boolean equation"
  let multiplicity ← c.memoryColumns request.multiplicity 1
  let kind ← c.memoryColumns request.delegation_type 1
  let offset ← c.memoryColumns request.abi_mem_offset_high 1
  pure ⟨address,value,time,limbs,#v[borrowLow,borrowHigh],multiplicity[0]!,kind[0]!,offset[0]!,3⟩

/-- Validate every consumed local expression and physical descriptor. Reduced
    initialization/request metadata cannot bypass checks through a typed value. -/
def Circuit.validate (c : Circuit) : Except String Unit := do
  c.validateLocal
  let _ ← c.requestColumns
  if c.memory_layout.intermediate_state_layout.isSome || c.memory_layout.machine_state_layout.isSome then
    let _ ← c.memoryPorts
    let _ ← c.decoderColumns
  if c.hasReducedLookups then
    let _ ← c.reducedArgumentColumns

def parseCircuit (source : String) : Except String Circuit := do
  let json ← Json.parse source
  let c : Circuit ← fromJson? json
  c.validate
  pure c

def loadCircuit (path : System.FilePath) : IO (Except String Circuit) :=
  parseCircuit <$> IO.FS.readFile path

end Airbender
