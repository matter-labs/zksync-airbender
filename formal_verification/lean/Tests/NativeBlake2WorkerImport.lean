import Airbender.Review.Circuits.Blake2Worker.NativeArtifact

open Airbender Lean
set_option autoImplicit false

private def check (ok : Bool) (label : String) : IO Unit :=
  if ok then IO.println s!"PASS {label}" else throw (IO.userError label)

private def rejected {α : Type} : Except String α → Bool
  | .error _ => true | .ok _ => false

private def replaceField (json : Json) (key : String) (value : Json) : Except String Json := do
  let object ← json.getObj?
  return Json.mkObj (object.toArray.toList.filter (fun entry => entry.1 != key) ++ [(key,value)])

private def changed (json : Json) (key : String) (value : Json) : IO Unit := do
  let altered ← IO.ofExcept (replaceField json key value)
  check (rejected (Airbender.Import.Blake2Worker.parse altered.compress)) s!"worker rejects {key}"

private def changedNested (json : Json) (part key : String) (value : Json) : IO Unit := do
  let body ← IO.ofExcept (json.getObjVal? part)
  let altered ← IO.ofExcept (replaceField body key value)
  changed json part altered

def main : IO UInt32 := do
  try
    let source ← IO.FS.readFile "artifacts/circuits/blake2-native-layout.json"
    check (source == Airbender.Blake2Worker.Native.constraintsSourceBytes) "worker complete same-read source"
    let c ← IO.ofExcept (Airbender.Import.Blake2Worker.parse source)
    check (c.quadratics.size == 301 && c.linears.size == 51 && c.ranges.size == 2 &&
      c.clocks.size == 86 && c.queries.size == 208 && c.mapping.entries.size == 871) "complete local worker obligations"
    check (rejected (Airbender.parseCircuit source)) "main-circuit importer still rejects active workers"
    let json ← IO.ofExcept (Json.parse source)
    changed json "trace_len" (toJson (8388608 : Nat))
    changed json "executor_family_decoder_table_size" (toJson (1048576 : Nat))
    changed json "total_tables_size" (toJson (344383 : Nat))
    changed json "extra" Json.null
    changed json "degree_2_constraints" (toJson (#[] : Array Json))
    changed json "public_inputs" (toJson #[toJson (0 : Nat)])
    changedNested json "witness_layout" "range_check_16_lookup_expressions" (toJson (#[] : Array Json))
    changedNested json "witness_layout" "timestamp_range_check_lookup_expressions" (toJson (#[] : Array Json))
    changedNested json "witness_layout" "total_width" (toJson (647 : Nat))
    changedNested json "memory_layout" "total_width" (toJson (225 : Nat))
    changedNested json "memory_layout" "delegation_processor_layout" Json.null
    changedNested json "memory_layout" "delegation_request_layout" (Json.mkObj [])
    changedNested json "memory_layout" "register_and_indirect_accesses" (toJson (#[] : Array Json))
    changedNested json "setup_layout" "total_width" (toJson (7 : Nat))
    let memory ← IO.ofExcept (json.getObjVal? "memory_layout")
    let processor ← IO.ofExcept (memory.getObjVal? "delegation_processor_layout")
    let crossed ← IO.ofExcept (replaceField processor "write_timestamp" (toJson (⟨3,1⟩ : ColumnSet)))
    changedNested json "memory_layout" "delegation_processor_layout" crossed
    let queries ← IO.ofExcept ((← IO.ofExcept ((← IO.ofExcept (json.getObjVal? "witness_layout")).getObjVal? "width_3_lookups")).getArr?)
    let some first := queries[0]? | throw (IO.userError "missing query")
    let bad ← IO.ofExcept (replaceField first "table_index" (Json.mkObj [("Constant",toJson "RomRead")]))
    changedNested json "witness_layout" "width_3_lookups" (toJson (queries.set! 0 bad))
    let equations ← IO.ofExcept ((← IO.ofExcept (json.getObjVal? "degree_1_constraints")).getArr?)
    let some equation := equations[0]? | throw (IO.userError "missing equation")
    let forged ← IO.ofExcept (replaceField equation "constant_term" (toJson (2147483648 : Nat)))
    changed json "degree_1_constraints" (toJson (equations.set! 0 forged))
    let mapping ← IO.ofExcept (json.getObjVal? "variable_mapping")
    let duplicate ← IO.ofExcept (replaceField mapping "00" (toJson (ColumnAddress.MemorySubtree 0)))
    changed json "variable_mapping" duplicate
    let outOfBounds ← IO.ofExcept (replaceField mapping "0" (toJson (ColumnAddress.MemorySubtree 226)))
    changed json "variable_mapping" outOfBounds
    let redundantZero ← IO.ofExcept (replaceField equation "constant_term" (toJson (2147483647 : Nat)))
    let redundantSource ← IO.ofExcept (replaceField json "degree_1_constraints" (toJson (equations.set! 0 redundantZero)))
    let redundantArtifact ← IO.ofExcept (Airbender.Import.Blake2Worker.parse redundantSource.compress)
    let some zeroEquation := redundantArtifact.linears[0]? | throw (IO.userError "missing redundant-zero equation")
    check (zeroEquation.constant_term.canonical == 0) "native redundant modulus encoding is zero"
    -- Canonical changed coefficients are faithfully read, not certified by intake.
    let altered ← IO.ofExcept (replaceField equation "constant_term" (toJson (1 : Nat)))
    let positive ← IO.ofExcept (replaceField json "degree_1_constraints" (toJson (equations.set! 0 altered)))
    let changedArtifact ← IO.ofExcept (Airbender.Import.Blake2Worker.parse positive.compress)
    let some alteredEquation := changedArtifact.linears[0]? | throw (IO.userError "missing changed equation")
    check (alteredEquation.constant_term.canonical == 1) "intake preserves changed equations without asserting semantics"
    return (0 : UInt32)
  catch error =>
    IO.eprintln s!"FAIL {error}"
    return (1 : UInt32)
