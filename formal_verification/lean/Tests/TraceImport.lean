import Airbender.Import.Parse
import Airbender.Review.AddSub.Artifact
import Airbender.Review.WordMemory.Artifact
import Tests.Timestamps

namespace Tests.TraceImport
open Airbender
set_option warningAsError true

private def check (ok : Bool) (label : String) : IO Unit :=
  if ok then IO.println s!"PASS {label}" else throw (IO.userError s!"FAIL {label}")

private def rejected {α : Type} : Except String α → Bool
  | .error _ => true
  | .ok _ => false

def run : IO Unit := do
  let source ← IO.FS.readFile "../../cs/compiled_circuits/add_sub_lui_auipc_mop_layout_no_caches_gkr.json"
  let .ok c := parseCircuit source | throw (IO.userError "no-cache artifact failed import")
  let .ok clock := c.traceColumns | throw (IO.userError "clock metadata import failed")
  let .ok timestampQueries := c.timestampExpressions | throw (IO.userError "timestamp query import failed")
  check (clock == AddSub.importedConstraintsTraceColumns && timestampQueries.size == 8 &&
    source == AddSub.importedConstraintsSourceBytes)
    "ADD/SUB: eight native timestamp queries and placement-resolved clock ports"
  check (rejected (Circuit.traceColumns {c with memory_layout :=
    {c.memory_layout with machine_state := none}})) "trace metadata without machine state rejected"
  check (rejected (Circuit.traceColumns {c with aux_layout_data :=
    {c.aux_layout_data with shuffle_ram_timestamp_comparison_aux_vars := #[]}}))
    "trace metadata with missing timestamp borrows rejected"
  check (rejected (Circuit.traceColumns {c with timestamp_range_check_lookup_expressions := #[]}))
    "trace metadata with missing timestamp queries rejected"
  check (rejected (Circuit.timestampExpressions {c with placement_data :=
    ⟨c.placement_data.entries.filter (fun (v, _) => v != 21)⟩}))
    "timestamp query with missing logical placement rejected"
  check (rejected (Circuit.traceColumns {c with placement_data :=
    ⟨c.placement_data.entries.push (999, .BaseLayerMemory 20)⟩}))
    "timestamp metadata with ambiguous state placement rejected"
  let some firstTimestamp := c.timestamp_range_check_lookup_expressions[0]?
    | throw (IO.userError "missing timestamp query")
  let reordered := {firstTimestamp with lookup_set_index := 1}
  check (rejected (Circuit.timestampExpressions {c with timestamp_range_check_lookup_expressions :=
    (c.timestamp_range_check_lookup_expressions.set! 0 reordered)}))
    "timestamp query with reordered native set index rejected"
  let some (RamQuery.Readonly firstPort) := c.memory_layout.ram_access_sets[0]?
    | throw (IO.userError "missing register timestamp port")
  check (rejected (Circuit.traceColumns {c with memory_layout := {c.memory_layout with
    ram_access_sets := c.memory_layout.ram_access_sets.set! 0
      (.Readonly {firstPort with in_cycle_write_index := ⟨3, by decide⟩})}}))
    "timestamp port with incorrect in-cycle offset rejected"
  let wordSource ← IO.FS.readFile "../../cs/compiled_circuits/mem_word_only_layout_no_caches_gkr.json"
  let .ok word := parseCircuit wordSource | throw (IO.userError "word-memory artifact failed import")
  let .ok wordClock := word.traceColumns | throw (IO.userError "word-memory clock metadata import failed")
  let .ok wordTimestamps := word.timestampExpressions | throw (IO.userError "word-memory timestamp import failed")
  check (wordClock == WordMemory.importedConstraintsTraceColumns && wordTimestamps.size == 8 &&
    wordSource == WordMemory.importedConstraintsSourceBytes)
    "word-memory: eight native timestamp queries and placement-resolved clock ports"

-- A focused target runs these guards without rebuilding unrelated circuit proofs.
#eval run

end Tests.TraceImport
