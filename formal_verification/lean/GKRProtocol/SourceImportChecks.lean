import GKRProtocol.Source

open Lean Elab Command Airbender.Compiler
set_option warningAsError true

/- Exercise the complete typed semantic-input schema against every actual
pre-compiler source capture. This checks the importer, not protocol soundness. -/
run_cmd do
  for family in ["add-sub", "jump-branch", "mul-div", "shift-binop", "word-memory",
      "subword-memory", "unified", "bigint", "blake-g", "blake-round", "keccak"] do
    for mode in ["cached", "uncached"] do
      let path := s!"artifacts/compiler/{family}-{mode}-source.json"
      let bytes ← IO.FS.readFile path
      let snapshot ← match Json.parse bytes >>= (fromJson? (α := Source.Snapshot)) with
        | .ok snapshot => pure snapshot
        | .error error => throwError "{path}: {error}"
      unless snapshot.format_version == 1 && snapshot.family == family &&
          snapshot.cached == (mode == "cached") do
        throwError "wrong source capture identity: {path}"
      unless snapshot.semantic_inputs.lookups.size == snapshot.source.remaining_inputs.lookups &&
          snapshot.semantic_inputs.range_checks.size == snapshot.source.remaining_inputs.range_checks &&
          snapshot.semantic_inputs.memory_queries.size == snapshot.source.remaining_inputs.memory_queries &&
          snapshot.semantic_inputs.register_and_indirect_accesses.size ==
            snapshot.source.remaining_inputs.register_and_indirect_accesses do
        throwError "source semantic input coverage differs: {path}"
