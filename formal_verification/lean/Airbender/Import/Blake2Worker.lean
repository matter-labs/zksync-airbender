import Airbender.Import.Embed
import Airbender.Review.Circuits.Blake2Worker.ABI

namespace Airbender.Import.Blake2Worker
open Lean Elab Command

/-- Local equations and every lookup are consumed. The full JSON is retained
    separately, including stage-two, indirect clock and protocol descriptors. -/
structure Artifact where
  raw : Json
  mapping : ObjectMap Nat ColumnAddress
  abi : Airbender.Blake2Worker.ABI
  quadratics : Array CompiledDegree2Constraint
  linears : Array CompiledDegree1Constraint
  ranges : Array LookupExpression
  clocks : Array LookupExpression
  queries : Array (Array LookupExpression × Nat)

private def exactKeys (json : Json) (keys : Array String) : Except String Unit := do
  let entries := (← json.getObj?).toArray
  unless entries.size == keys.size && entries.all (fun (key, _) => keys.contains key) do
    throw "unexpected or missing Blake2 layout fields"

private def read [FromJson α] (json : Json) (key : String) : Except String α := do
  fromJson? (← json.getObjVal? key)

private def empty (json : Json) (key : String) : Except String Unit := do
  unless (← (← json.getObjVal? key).getArr?).isEmpty do throw "unsupported nonempty Blake2 boundary"

private def isNull (json : Json) (key : String) : Except String Unit := do
  unless (← json.getObjVal? key) == .null do throw "unsupported Blake2 machine/caller layout"

private def group (json : Json) : Except String ColumnSet := do
  exactKeys json #["start","num_elements"]
  fromJson? json

private def expectGroup (json : Json) (key : String) (start count : Nat) : Except String Unit := do
  let value ← group (← json.getObjVal? key)
  unless value.start == start && value.num_elements == count do throw "unsupported Blake2 group geometry"

def Artifact.logical (c : Artifact) (address : ColumnAddress) : Except String Nat := do
  let inBounds : Bool := match address with
    | .WitnessSubtree n => decide (n < c.abi.witnessWidth)
    | .MemorySubtree n => decide (n < c.abi.memoryWidth)
    | .SetupSubtree n => decide (n < c.abi.setupWidth)
    | .OptimizedOut _ => false
  unless inBounds do throw "physical column outside Blake2 layout"
  match (c.mapping.entries.filter fun (_, a) => a == address).toList with
    | [(v, _)] => pure v
    | _ => throw "Blake2 physical column must have exactly one logical variable"

def Artifact.linear (c : Artifact) (q : CompiledDegree1Constraint) : Except String Expr := do
  let terms ← q.linear_terms.mapM fun (a,v) => do
    pure (.Product #[.Constant a,.Var (← c.logical v)] : Expr)
  pure (.Sum (#[.Constant q.constant_term] ++ terms))

def Artifact.quadratic (c : Artifact) (q : CompiledDegree2Constraint) : Except String Expr := do
  let terms ← q.quadratic_terms.mapM fun t => do
    pure (.Product #[.Constant t.first,.Var (← c.logical t.second),.Var (← c.logical t.third)] : Expr)
  pure (.Sum (#[← c.linear ⟨q.linear_terms,q.constant_term⟩] ++ terms))

def Artifact.lookup (c : Artifact) : LookupExpression → Except String Expr
  | .Variable a => Expr.Var <$> c.logical a
  | .Expression e => c.linear e

private def pair (c : Artifact) (j : Json) : Except String (Vector Nat 2) := do
  let g ← group j
  unless g.num_elements == 1 do throw "Blake2 word/time needs one two-column group"
  return #v[← c.logical (.MemorySubtree g.start),← c.logical (.MemorySubtree (g.start+1))]

private def access (c : Artifact) (j : Json) (indirect : Bool) : Except String (Nat × Airbender.Blake2Worker.Access) := do
  let entries := (← j.getObj?).toArray
  unless entries.size == 1 do throw "expected one native Blake2 access variant"
  let (tag,body) := entries[0]!
  unless tag == "ReadAccess" || tag == "WriteAccess" do throw "unsupported Blake2 access variant"
  let write := tag == "WriteAccess"
  let keys := #["read_timestamp","read_value"] ++ (if write then #["write_value"] else #[]) ++
    (if indirect then #["address_derivation_carry_bit","variable_dependent","offset_constant"] else #["register_index"])
  exactKeys body keys
  let time ← pair c (← body.getObjVal? "read_timestamp")
  let value ← pair c (← body.getObjVal? "read_value")
  let written ← if write then some <$> pair c (← body.getObjVal? "write_value") else pure none
  if indirect then
    expectGroup body "address_derivation_carry_bit" 0 0
    isNull body "variable_dependent"
  let index : Nat ← read body (if indirect then "offset_constant" else "register_index")
  return (index,⟨if indirect then index else 0,time,value,written⟩)

/-- Selected actual worker geometry only. Unknown active machine/batched
    boundaries fail closed; retained protocol metadata is not an acceptance claim. -/
def parse (source : String) : Except String Artifact := do
  let raw ← Json.parse source
  exactKeys raw #["witness_layout","memory_layout","setup_layout","stage_2_layout",
    "degree_2_constraints","degree_1_constraints","state_linkage_constraints","public_inputs",
    "variable_mapping","scratch_space_size_for_witness_gen","lazy_init_address_aux_vars",
    "memory_queries_timestamp_comparison_aux_vars","batched_memory_access_timestamp_comparison_aux_vars",
    "register_and_indirect_access_timestamp_comparison_aux_vars","executor_family_circuit_next_timestamp_aux_var",
    "executor_family_decoder_table_size","trace_len","table_offsets","total_tables_size"]
  let trace : Nat ← read raw "trace_len"
  let decoder : Nat ← read raw "executor_family_decoder_table_size"
  let scratch : Nat ← read raw "scratch_space_size_for_witness_gen"
  let rows : Nat ← read raw "total_tables_size"
  unless trace == 1048576 && decoder == 0 && scratch == 0 && rows == 344384 do
    throw "unsupported native Blake2 trace/setup geometry"
  for key in #["state_linkage_constraints","public_inputs","lazy_init_address_aux_vars","memory_queries_timestamp_comparison_aux_vars"] do empty raw key
  isNull raw "executor_family_circuit_next_timestamp_aux_var"
  let m ← raw.getObjVal? "memory_layout"
  exactKeys m #["shuffle_ram_inits_and_teardowns","shuffle_ram_access_sets","delegation_request_layout",
    "delegation_processor_layout","machine_state_layout","intermediate_state_layout","batched_ram_accesses",
    "register_and_indirect_accesses","total_width"]
  for key in #["shuffle_ram_inits_and_teardowns","shuffle_ram_access_sets","batched_ram_accesses"] do empty m key
  for key in #["delegation_request_layout","machine_state_layout","intermediate_state_layout"] do isNull m key
  let width : Nat ← read m "total_width"
  unless width == 226 do throw "unsupported Blake2 memory width"
  let processor ← m.getObjVal? "delegation_processor_layout"
  exactKeys processor #["multiplicity","abi_mem_offset_high","write_timestamp"]
  expectGroup processor "multiplicity" 0 1
  expectGroup processor "abi_mem_offset_high" 1 1
  expectGroup processor "write_timestamp" 2 1
  let w ← raw.getObjVal? "witness_layout"
  exactKeys w #["multiplicities_columns_for_range_check_16","multiplicities_columns_for_timestamp_range_check",
    "multiplicities_columns_for_decoder_in_executor_families","multiplicities_columns_for_generic_lookup",
    "range_check_8_columns","range_check_16_columns","width_3_lookups","range_check_16_lookup_expressions",
    "timestamp_range_check_lookup_expressions","offset_for_special_shuffle_ram_timestamps_range_check_expressions",
    "boolean_vars_columns_range","scratch_space_columns_range","total_width"]
  let ww : Nat ← read w "total_width"
  let special : Nat ← read w "offset_for_special_shuffle_ram_timestamps_range_check_expressions"
  unless ww == 648 && special == 86 do throw "unsupported Blake2 witness geometry"
  expectGroup w "multiplicities_columns_for_range_check_16" 0 1
  expectGroup w "multiplicities_columns_for_timestamp_range_check" 1 1
  expectGroup w "multiplicities_columns_for_decoder_in_executor_families" 0 0
  expectGroup w "multiplicities_columns_for_generic_lookup" 2 1
  expectGroup w "range_check_8_columns" 3 0
  expectGroup w "range_check_16_columns" 3 0
  expectGroup w "boolean_vars_columns_range" 3 168
  expectGroup w "scratch_space_columns_range" 611 37
  let setup ← raw.getObjVal? "setup_layout"
  exactKeys setup #["timestamp_setup_columns","range_check_16_setup_column","timestamp_range_check_setup_column",
    "generic_lookup_setup_columns","preprocessed_decoder_setup_columns","total_width"]
  let sw : Nat ← read setup "total_width"
  unless sw == 6 do throw "unsupported Blake2 setup width"
  expectGroup setup "timestamp_setup_columns" 0 0
  expectGroup setup "range_check_16_setup_column" 0 1
  expectGroup setup "timestamp_range_check_setup_column" 1 1
  expectGroup setup "generic_lookup_setup_columns" 2 1
  expectGroup setup "preprocessed_decoder_setup_columns" 0 0
  let offsets : Array Nat ← read raw "table_offsets"
  unless offsets == ((List.range 62).toArray.map fun id =>
    if id ≤ 4 then 0 else if id ≤ 26 then 65536 else if id == 27 then 65600
    else if id == 28 then 65856 else if id == 29 then 82240 else 344384) do
    throw "unsupported Blake2 fixed-table offsets"
  let q : Array CompiledDegree2Constraint ← read raw "degree_2_constraints"
  let l : Array CompiledDegree1Constraint ← read raw "degree_1_constraints"
  let ranges : Array LookupExpression ← read w "range_check_16_lookup_expressions"
  let clocks : Array LookupExpression ← read w "timestamp_range_check_lookup_expressions"
  let mut queries := #[]
  for query in (← (← w.getObjVal? "width_3_lookups").getArr?) do
    exactKeys query #["input_columns","table_index"]
    let inputs : Array LookupExpression ← read query "input_columns"
    unless inputs.size == 3 do throw "Blake2 lookup needs three inputs"
    let table ← query.getObjVal? "table_index"
    exactKeys table #["Constant"]
    let name : String ← read table "Constant"
    let id ← match name with
      | "Xor" => pure 4 | "Xor3" => pure 26 | "Xor4" => pure 27
      | "Xor7" => pure 28 | "Xor9" => pure 29
      | _ => throw "unsupported Blake2 fixed table"
    queries := queries.push (inputs,id)
  unless q.size == 301 && l.size == 51 && ranges.size == 2 && clocks.size == 86 && queries.size == 208 do
    throw "incomplete native Blake2 obligations"
  let mapping : ObjectMap Nat ColumnAddress ← read raw "variable_mapping"
  let c : Artifact := ⟨raw,mapping,⟨0,0,#v[0,0],#[],#[],trace,ww,width,sw,rows,0⟩,q,l,ranges,clocks,queries⟩
  unless mapping.entries.size == 871 && (mapping.entries.map Prod.fst).toList.Nodup do
    throw "duplicate or missing Blake2 logical variables"
  for (_,address) in mapping.entries do let _ ← c.logical address
  for equation in q do let _ ← c.quadratic equation
  for equation in l do let _ ← c.linear equation
  for expression in ranges ++ clocks do let _ ← c.lookup expression
  for (inputs,_) in queries do for expression in inputs do let _ ← c.lookup expression
  let mut registers := #[]
  for entry in (← (← m.getObjVal? "register_and_indirect_accesses").getArr?) do
    exactKeys entry #["register_access","indirect_accesses"]
    let (index,reg) ← access c (← entry.getObjVal? "register_access") false
    let mut indirects := #[]
    for item in (← (← entry.getObjVal? "indirect_accesses").getArr?) do
      let (_,item) ← access c item true
      indirects := indirects.push item
    registers := registers.push ⟨index,reg,indirects⟩
  unless registers.size == 3 do throw "unsupported Blake2 ABI register count"
  for slot in [:3] do
    let reg := registers[slot]!
    unless reg.register == 10+slot && reg.access.writeValue.isSome == (slot == 2) &&
      reg.indirects.size == (if slot == 0 then 24 else if slot == 1 then 16 else 0) do
      throw "unsupported Blake2 ABI register/indirect geometry"
    for i in [:reg.indirects.size] do
      let item := reg.indirects[i]!
      unless item.offset == 4*i && item.writeValue.isSome == (slot == 0) do
        throw "unsupported Blake2 indirect access geometry"
  let stage ← raw.getObjVal? "stage_2_layout"
  let aux ← group (← stage.getObjVal? "delegation_processing_aux_poly")
  unless aux.num_elements == 1 do throw "missing Blake2 processing auxiliary"
  let abi : Airbender.Blake2Worker.ABI := ⟨← c.logical (.MemorySubtree 0),← c.logical (.MemorySubtree 1),
    ← pair c (← processor.getObjVal? "write_timestamp"),registers,
    ← (Array.range 168).mapM (fun i => c.logical (.WitnessSubtree (3+i))),trace,ww,width,sw,rows,aux.start⟩
  return {c with abi}

private def constantSyntax (n : Int) : CommandElabM (TSyntax `term) := do
  let value ← if n ≥ 0 then `(Int.ofNat $(quote n.toNat)) else `(Int.negSucc $(quote (-n-1).toNat))
  `(_root_.Expression.const (Int.cast $value))

private partial def exprSyntax (e : Expr) : CommandElabM (TSyntax `term) := do
  match e with
  | .Constant c => constantSyntax (Artifact.signedCoefficient c)
  | .Var v => `(_root_.Expression.var ⟨$(quote v)⟩)
  | .Sum es => es.foldlM (fun acc e => do `(_root_.Expression.add $acc $(← exprSyntax e))) (← constantSyntax 0)
  | .Product es => es.foldlM (fun acc e => do `(_root_.Expression.mul $acc $(← exprSyntax e))) (← constantSyntax 1)

private def pairSyntax (v : Vector Nat 2) : CommandElabM (TSyntax `term) :=
  `(#v[$(quote v[0]),$(quote v[1])])

private def accessSyntax (a : Airbender.Blake2Worker.Access) : CommandElabM (TSyntax `term) := do
  let written ← match a.writeValue with | none => `(none) | some v => `(some $(← pairSyntax v))
  `(Airbender.Blake2Worker.Access.mk $(quote a.offset) $(← pairSyntax a.readTime) $(← pairSyntax a.readValue) $written)

/-- Complete local native row intake. Each emitted block is small; neither
    indirect memory matching nor protocol auxiliary acceptance is fabricated. -/
elab "import_native_blake2 " name:ident " from " path:str : command => do
  let source ← IO.FS.readFile path.getString
  let c ← match parse source with | .ok c => pure c | .error e => throwError "Blake2 import failed: {e}"
  let expressions ← match do pure ((← c.quadratics.mapM c.quadratic) ++ (← c.linears.mapM c.linear)) with
    | .ok es => pure es | .error e => throwError e
  let mut ops ← expressions.mapM fun e => do `(_root_.FlatOperation.assert $(← exprSyntax e))
  for e in c.ranges do
    let e ← match c.lookup e with | .ok e => pure e | .error e => throwError e
    ops := ops.push (← `(_root_.FlatOperation.lookup (Verification.range16 $(← exprSyntax e))))
  for e in c.clocks do
    let e ← match c.lookup e with | .ok e => pure e | .error e => throwError e
    ops := ops.push (← `(_root_.FlatOperation.lookup (Verification.timestamp19 $(← exprSyntax e))))
  let setup := mkIdent `setup
  for (inputs,id) in c.queries do
    let entries ← inputs.mapM fun e => do
      match c.lookup e with | .ok e => exprSyntax e | .error e => throwError e
    let tag ← constantSyntax id
    ops := ops.push (← `(_root_.FlatOperation.lookup {
      table := ($setup).toRaw
      entry := #v[$(entries[0]!),$(entries[1]!),$(entries[2]!),$tag]}))
  let mut blocks := #[]
  for index in [: (ops.size+63)/64] do
    let block := mkIdent (name.getId.appendAfter s!"Block{index}")
    let items := ops.extract (64*index) (min ops.size (64*(index+1)))
    elabCommand (← `(def $block {p : Nat} [Fact (Nat.Prime p)]
      ($setup : _root_.Table (ZMod p) (_root_.fields 4)) : List (_root_.FlatOperation (ZMod p)) := [$[$items],*]))
    blocks := blocks.push (← `($block $setup))
  let combined ← blocks.foldlM (fun acc block => do `($acc ++ $block)) (← `([]))
  elabCommand (← `(def $name {p : Nat} [Fact (Nat.Prime p)]
    ($setup : _root_.Table (ZMod p) (_root_.fields 4)) : List (_root_.FlatOperation (ZMod p)) := $combined))
  let mut registers := #[]
  for reg in c.abi.registers do
    let indirects ← reg.indirects.mapM accessSyntax
    registers := registers.push (← `(Airbender.Blake2Worker.RegisterAccess.mk $(quote reg.register)
      $(← accessSyntax reg.access) #[$[$indirects],*]))
  let abiName := mkIdent (name.getId.appendAfter "ABI")
  elabCommand (← `(def $abiName : Airbender.Blake2Worker.ABI :=
    ⟨$(quote c.abi.multiplicity),$(quote c.abi.offsetHigh),$(← pairSyntax c.abi.writeTime),#[$[$registers],*],
      $(quote c.abi.booleanColumns),$(quote c.abi.traceLength),$(quote c.abi.witnessWidth),$(quote c.abi.memoryWidth),
      $(quote c.abi.setupWidth),$(quote c.abi.genericRows),$(quote c.abi.processingAux)⟩))
  let bytesName := mkIdent (name.getId.appendAfter "SourceBytes")
  elabCommand (← `(def $bytesName : String := $(quote source)))

end Airbender.Import.Blake2Worker
