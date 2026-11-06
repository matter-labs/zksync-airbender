import Airbender.Review.Circuits.ReducedMachine.Artifact

open Airbender Lean
set_option autoImplicit false

private def check (ok : Bool) (label : String) : IO Unit :=
  if ok then IO.println s!"PASS {label}" else throw (IO.userError label)

private def rejected {α : Type} : Except String α → Bool
  | .error _ => true | .ok _ => false

private def replaceField (j : Json) (name : String) (value : Json) : Except String Json := do
  let object ← j.getObj?
  pure (Json.mkObj (object.toArray.toList.filter (fun entry => entry.1 != name) ++ [(name,value)]))

private def replacePath (json : Json) (path : List String) (value : Json) : Except String Json := do
  match path with
  | [] => pure value
  | name :: rest =>
    let child ← json.getObjVal? name
    replaceField json name (← replacePath child rest value)

private def changed (source : Json) (path : List String) (text : String) : IO Unit := do
  let value ← IO.ofExcept (Json.parse text)
  let altered ← IO.ofExcept (replacePath source path value)
  check (rejected (parseCircuit altered.compress)) s!"reduced rejects {path}"

def main : IO UInt32 := do
  try
    let source ← IO.FS.readFile "../../cs/reduced_machine_preprocessed_layout.json"
    check (source == ReducedMachine.importedConstraintsSourceBytes) "complete reduced source bytes match the compiled artifact"
    let json ← IO.ofExcept (Json.parse source)
    let c ← IO.ofExcept (parseCircuit source)
    check c.hasReducedLookups "actual reduced six-slot lookup profile"
    check (c.degree_2_constraints.size == 114 && c.degree_1_constraints.size == 5 &&
      c.variable_mapping.entries.size == 141) "all native reduced equations and variables"
    check (c.witness_layout.range_check_16_lookup_expressions.size == 8 &&
      c.witness_layout.timestamp_range_check_lookup_expressions.size == 8 &&
      c.witness_layout.width_3_lookups.size == 6) "all native reduced query slots retained"
    let setup ← IO.ofExcept c.setupColumns
    check (setup.traceLength == 8388608 && setup.width == 16 && setup.genericRows == 5705985 &&
      setup.decoderStart == 6 && setup.decoderCapacity == 1048576) "actual log-23 reduced setup geometry"
    let clocks ← IO.ofExcept c.traceColumns
    check (clocks.execute == 4 && clocks.initialPC == #v[0,1] && clocks.finalPC == #v[13,14] &&
      clocks.initialTime == #v[2,3] && clocks.finalTime == #v[15,16] && clocks.ports.size == 3)
      "actual reduced state and direct-port clocks"
    let ports ← IO.ofExcept c.memoryPorts
    check (ports.size == 3) "all reduced direct memory ports retained"
    let decoder ← IO.ofExcept c.decoderColumns
    check (decoder.rs1 == 5 && decoder.rs2 == 6 && decoder.rd == 7 && decoder.rdIsZero == 8 &&
      decoder.immediate == #v[9,10] && decoder.funct3 == 11 && decoder.mask == 12)
      "original reduced decoder column order"
    let args ← IO.ofExcept c.reducedArgumentColumns
    check (args.initialAddress == #v[125,126] && args.terminalValue == #v[127,128] &&
      args.terminalTime == #v[129,130]) "actual reduced init and teardown coordinates"
    check (args.addressAux == #v[121,122] && args.addressBorrows == #v[123,124])
      "actual reduced initialization auxiliary coordinates"
    check (args.requestMultiplicity == 91 && args.requestType == 93 && args.requestOffsetHigh == 92 &&
      args.requestClockOffset == 3) "actual reduced delegation request coordinates"
    let standalone ← IO.ofExcept (parseCircuit (← IO.FS.readFile
      "../../cs/add_sub_lui_auipc_mop_preprocessed_layout.json"))
    check (rejected ({standalone with memory_layout := {standalone.memory_layout with
      delegation_request_layout := c.memory_layout.delegation_request_layout}}.validate))
      "reject reduced request metadata on a standalone profile"
    check ((← IO.ofExcept c.requestColumns) == some ⟨91,93,some 92,3⟩)
      "actual reduced request has a retained ABI high column"
    let shift ← IO.ofExcept (parseCircuit (← IO.FS.readFile
      "../../cs/shift_binop_csrrw_preprocessed_layout.json"))
    check ((← IO.ofExcept shift.requestColumns) == some ⟨37,38,none,3⟩)
      "actual shift CSR request retains its absent ABI group"
    check (rejected ({shift with memory_layout := {shift.memory_layout with
      delegation_request_layout := none}}.validate)) "reject missing native shift CSR request"
    let some shiftRequest := shift.memory_layout.delegation_request_layout
      | throw (IO.userError "missing native shift CSR request")
    check (rejected ({shift with memory_layout := {shift.memory_layout with
      delegation_request_layout := some {shiftRequest with abi_mem_offset_high := ⟨0,1⟩}}}.validate))
      "reject invented shift CSR ABI column rather than aliasing memory zero"
    let stage ← IO.ofExcept (json.getObjVal? "stage_2_layout")
    check (c.stage_2_layout.raw.compress == stage.compress)
      "stage-two descriptor retained verbatim without an enforcement claim"
    for q in c.degree_2_constraints do
      let _ ← IO.ofExcept (c.quadraticExpression q)
    for q in c.degree_1_constraints do
      let _ ← IO.ofExcept (c.linearExpression q)
    for q in c.witness_layout.width_3_lookups do
      for entry in q.input_columns do
        let _ ← IO.ofExcept (c.lookupExpression entry)
    check true "every actual reduced equation and tagged expression resolves"
    changed json ["trace_len"] "16777216"
    changed json ["executor_family_decoder_table_size"] "524288"
    changed json ["total_tables_size"] "5705984"
    changed json ["setup_layout","preprocessed_decoder_setup_columns"] "{\"start\":5,\"num_elements\":1}"
    changed json ["memory_layout","shuffle_ram_inits_and_teardowns"] "[]"
    changed json ["lazy_init_address_aux_vars"] "[]"
    changed json ["memory_layout","delegation_request_layout"] "null"
    changed json ["memory_layout","delegation_processor_layout"] "{}"
    changed json ["memory_layout","batched_ram_accesses"] "[{}]"
    changed json ["memory_layout","register_and_indirect_accesses"] "[{}]"
    changed json ["public_inputs"] "[0]"
    changed json ["stage_2_layout"] "null"
    changed json ["memory_layout","delegation_request_layout","in_cycle_write_index"] "2"
    changed json ["memory_layout","delegation_request_layout","multiplicity"] "{\"start\":39,\"num_elements\":1}"
    changed json ["memory_layout","delegation_request_layout","abi_mem_offset_high"] "{\"start\":0,\"num_elements\":0}"
    changed json ["memory_layout","delegation_request_layout","abi_mem_offset_high"] "{\"start\":28,\"num_elements\":1}"
    changed json ["memory_layout","machine_state_layout","pc"] "{\"start\":38,\"num_elements\":1}"
    changed json ["batched_memory_access_timestamp_comparison_aux_vars","predicate"] "{\"WitnessSubtree\":19}"
    changed json ["batched_memory_access_timestamp_comparison_aux_vars","aux_borrow_vars"] "[{\"WitnessSubtree\":19}]"
    changed json ["register_and_indirect_access_timestamp_comparison_aux_vars","aux_borrow_sets"] "[[]]"
    let some init := c.memory_layout.shuffle_ram_inits_and_teardowns[0]?
      | throw (IO.userError "missing native initialization")
    check (rejected ({c with memory_layout := {c.memory_layout with
      shuffle_ram_inits_and_teardowns := #[{init with lazy_init_addresses_columns := ⟨38,1⟩}]}}.reducedArgumentColumns))
      "reject init address crossing native memory extent"
    check (rejected ({c with memory_layout := {c.memory_layout with
      shuffle_ram_inits_and_teardowns := #[{init with lazy_teardown_values_columns := ⟨2,0⟩}]}}.reducedArgumentColumns))
      "reject missing native teardown value group"
    let some aux := c.lazy_init_address_aux_vars[0]?
      | throw (IO.userError "missing native initialization auxiliary")
    check (rejected ({c with lazy_init_address_aux_vars := #[{aux with aux_low_high := #[.WitnessSubtree 17]}]}.reducedArgumentColumns))
      "reject initialization auxiliary with wrong arity"
    check (rejected ({c with lazy_init_address_aux_vars := #[{aux with intermediate_borrow := .WitnessSubtree 50}]}.reducedArgumentColumns))
      "reject initialization borrow without native Boolean equation"
    let lookups := c.witness_layout.width_3_lookups
    let some slot := lookups[2]? | throw (IO.userError "missing native lookup slot")
    let bad := {slot with table_index := .Variable (.WitnessSubtree 59)}
    check (rejected ({c with witness_layout := {c.witness_layout with width_3_lookups := lookups.set! 2 bad}}.validate))
      "reject changed native reduced dynamic selector profile"
    let offsets := c.table_offsets.set! 25 1507584
    check (rejected ({c with table_offsets := offsets}.validate)) "reject altered reduced native table offset"
    return (0 : UInt32)
  catch error =>
    IO.eprintln s!"FAIL {error}"
    return (1 : UInt32)
