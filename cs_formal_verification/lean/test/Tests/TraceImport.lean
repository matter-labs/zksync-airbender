import Human.Import.Parse
import Slop.AddSub.ArtifactChecks
import Human.Circuits.WordMemory.Artifact
import Human.Circuits.JumpBranchSlt.Artifact
import Slop.ShiftBinop.ArtifactChecks
import Human.Circuits.SubwordMemory.Artifact
import Tests.Timestamps
import Tests.TraceHistory

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
  let .ok ports := c.memoryPorts | throw (IO.userError "memory metadata import failed")
  check (clock == AddSub.importedConstraintsTraceColumns && timestampQueries.size == 8 &&
    source == AddSub.importedConstraintsSourceBytes)
    "ADD/SUB: eight native timestamp queries and placement-resolved clock ports"
  check (ports == AddSub.importedConstraintsMemoryPorts && ports.map (·.clock) == clock.ports)
    "ADD/SUB: native register addresses, old/new values and clock descriptors"
  let .ok decoder := c.decoderColumns | throw (IO.userError "decoder metadata import failed")
  check (decoder == AddSub.importedConstraintsDecoderColumns)
    "ADD/SUB: native decoder registers, immediate and nine selector bits"
  check (rejected (Circuit.decoderColumns {c with memory_layout :=
    {c.memory_layout with decoder_input := none}})) "missing decoder metadata rejected"
  check (rejected (Circuit.decoderColumns {c with placement_data :=
    ⟨c.placement_data.entries.filter (fun (v, _) => v != 8)⟩}))
    "decoder immediate with missing logical placement rejected"
  check (rejected (Circuit.decoderColumns {c with placement_data :=
    ⟨c.placement_data.entries.push (999, .BaseLayerWitness 2)⟩}))
    "decoder selector with ambiguous logical placement rejected"
  let some decoderInput := c.memory_layout.decoder_input | throw (IO.userError "missing decoder input")
  check (rejected (Circuit.decoderColumns {c with memory_layout := {c.memory_layout with
    decoder_input := some {decoderInput with imm := ⟨#[c.witness_layout.total_width, 1], by simp⟩}}}))
    "decoder immediate outside its declared storage bank rejected"
  let .ok memoryDecoder := Circuit.decoderColumns {c with memory_layout := {c.memory_layout with
    decoder_input := some {decoderInput with decoder_witness_is_in_memory := true}}}
    | throw (IO.userError "memory-bank decoder metadata failed import")
  check (memoryDecoder.immediate == #v[23, 24] && memoryDecoder != decoder)
    "decoder immediate storage-bank polarity survives import"
  check (rejected (Circuit.memoryPorts {c with placement_data :=
    ⟨c.placement_data.entries.filter (fun (v, _) => v != 5)⟩}))
    "register port with missing address placement rejected"
  check (rejected (Circuit.memoryPorts {c with placement_data :=
    ⟨c.placement_data.entries.push (999, .BaseLayerMemory 15)⟩}))
    "write port with ambiguous value placement rejected"
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
  let .ok zeroPorts := Circuit.memoryPorts {c with memory_layout := {c.memory_layout with
    ram_access_sets := c.memory_layout.ram_access_sets.set! 0
      (.Readonly {firstPort with read_value := .Zero})}}
    | throw (IO.userError "explicit zero memory port import failed")
  let some zeroPort := zeroPorts[0]? | throw (IO.userError "missing zero memory port")
  check (zeroPort.readValue == .zero) "explicit zero memory port retained"
  let wordSource ← IO.FS.readFile "../../cs/compiled_circuits/mem_word_only_layout_no_caches_gkr.json"
  let .ok word := parseCircuit wordSource | throw (IO.userError "word-memory artifact failed import")
  let .ok wordClock := word.traceColumns | throw (IO.userError "word-memory clock metadata import failed")
  let .ok wordTimestamps := word.timestampExpressions | throw (IO.userError "word-memory timestamp import failed")
  let .ok wordPorts := word.memoryPorts | throw (IO.userError "word-memory port import failed")
  check (wordClock == WordMemory.importedConstraintsTraceColumns && wordTimestamps.size == 8 &&
    wordSource == WordMemory.importedConstraintsSourceBytes)
    "word-memory: eight native timestamp queries and placement-resolved clock ports"
  check (wordPorts == WordMemory.importedConstraintsMemoryPorts &&
    wordPorts.map (·.clock) == wordClock.ports)
    "word-memory: opposite register/RAM polarities and all read/write columns"
  let .ok wordDecoder := word.decoderColumns | throw (IO.userError "word decoder metadata import failed")
  check (wordDecoder == WordMemory.importedConstraintsDecoderColumns)
    "word-memory: native decoder registers, immediate and store selector"
  let some (RamQuery.Readonly mixedPort) := word.memory_layout.ram_access_sets[1]?
    | throw (IO.userError "missing mixed memory port")
  let .RegisterOrRam mixed := mixedPort.address | throw (IO.userError "missing mixed address")
  let changedAddress : RamAddress := .RegisterOrRam {mixed with address_space := .RamAddressSpace 9}
  let changedPort := {mixedPort with address := changedAddress}
  let changed := {word with memory_layout := {word.memory_layout with ram_access_sets :=
    (word.memory_layout.ram_access_sets.set! 1 (.Readonly changedPort))}}
  let .ok changedPorts := Circuit.memoryPorts changed | throw (IO.userError "changed polarity failed import")
  check (changedPorts[1]?.map (·.address) == some (.mixed 10 false #v[19, 20]) &&
    changedPorts != wordPorts) "native address-space polarity survives import"

  let jumpSource ← IO.FS.readFile "../../cs/compiled_circuits/jump_branch_slt_layout_no_caches_gkr.json"
  let .ok jump := parseCircuit jumpSource | throw (IO.userError "jump/branch/SLT artifact failed import")
  let .ok jumpClock := jump.traceColumns | throw (IO.userError "jump/branch/SLT clock import failed")
  let .ok jumpTimestamps := jump.timestampExpressions | throw (IO.userError "jump/branch/SLT timestamps failed")
  let .ok jumpPorts := jump.memoryPorts | throw (IO.userError "jump/branch/SLT ports failed")
  let .ok jumpDecoder := jump.decoderColumns | throw (IO.userError "jump/branch/SLT decoder failed")
  check (jumpClock == JumpBranchSlt.importedConstraintsTraceColumns && jumpTimestamps.size == 8 &&
    jumpSource == JumpBranchSlt.importedConstraintsSourceBytes)
    "jump/branch/SLT: eight native timestamp queries and placement-resolved clocks"
  check (jumpPorts == JumpBranchSlt.importedConstraintsMemoryPorts &&
    jumpPorts.map (·.clock) == jumpClock.ports)
    "jump/branch/SLT: native direct register ports and clock descriptors"
  check (jumpDecoder == JumpBranchSlt.importedConstraintsDecoderColumns &&
    jumpDecoder.funct3 == some 10 && jumpDecoder.flags.size == 5)
    "jump/branch/SLT: native funct3 and five selector bits"
  check (rejected (Circuit.decoderColumns {jump with placement_data :=
    ⟨jump.placement_data.entries.filter (fun (v, _) => v != 10)⟩}))
    "jump/branch/SLT: missing funct3 placement rejected"

  let shiftSource ← IO.FS.readFile "../../cs/compiled_circuits/shift_binop_layout_no_caches_gkr.json"
  let .ok shift := parseCircuit shiftSource | throw (IO.userError "shift/binop import failed")
  let .ok shiftPorts := shift.memoryPorts | throw (IO.userError "byte port import failed")
  let .ok shiftClock := shift.traceColumns | throw (IO.userError "shift clock import failed")
  let .ok shiftDecoder := shift.decoderColumns | throw (IO.userError "shift decoder import failed")
  check (shiftPorts == ShiftBinop.importedConstraintsMemoryPorts &&
    shiftPorts.map (·.clock) == shiftClock.ports)
    "shift/binop: native byte sources, two-limb destination and clock descriptors"
  check (shiftDecoder == ShiftBinop.importedConstraintsDecoderColumns &&
    shiftDecoder.funct3 == some 10 && shiftDecoder.flags.size == 2)
    "shift/binop: native funct3 and two selector bits"
  check (rejected (Circuit.memoryPorts {shift with placement_data :=
    ⟨shift.placement_data.entries.filter (fun (v, _) => v != 20)⟩}))
    "shift/binop: missing byte placement rejected"
  let some (RamQuery.Readonly firstBytePort) := shift.memory_layout.ram_access_sets[0]?
    | throw (IO.userError "expected readonly byte source")
  let invalidBytePort := RamQuery.Readonly {firstBytePort with
    read_value := .U8Limbs ⟨#[2, 3, 4, shift.memory_layout.total_width], by simp⟩}
  check (rejected (Circuit.memoryPorts {shift with memory_layout :=
    {shift.memory_layout with ram_access_sets :=
      shift.memory_layout.ram_access_sets.set! 0 invalidBytePort}}))
    "shift/binop: byte outside memory layout rejected"

  let subwordSource ← IO.FS.readFile "../../cs/compiled_circuits/mem_subword_only_layout_no_caches_gkr.json"
  let .ok subword := parseCircuit subwordSource | throw (IO.userError "subword-memory import failed")
  let .ok subwordClock := subword.traceColumns | throw (IO.userError "subword clock import failed")
  let .ok subwordTimestamps := subword.timestampExpressions | throw (IO.userError "subword timestamp import failed")
  let .ok subwordPorts := subword.memoryPorts | throw (IO.userError "subword port import failed")
  let .ok subwordDecoder := subword.decoderColumns | throw (IO.userError "subword decoder import failed")
  check (subwordClock == SubwordMemory.importedConstraintsTraceColumns && subwordTimestamps.size == 8 &&
    subwordSource == SubwordMemory.importedConstraintsSourceBytes)
    "subword-memory: eight native timestamp queries and placement-resolved clocks"
  check (subwordPorts == SubwordMemory.importedConstraintsMemoryPorts &&
    subwordPorts.map (·.clock) == subwordClock.ports)
    "subword-memory: native mixed register/RAM read/write ports and clocks"
  check (subwordDecoder == SubwordMemory.importedConstraintsDecoderColumns &&
    subwordDecoder.funct3 == none && subwordDecoder.flags.size == 3)
    "subword-memory: native immediate and store/byte/signed selectors"

-- A focused target runs these guards without rebuilding unrelated circuit proofs.
#eval run

end Tests.TraceImport
