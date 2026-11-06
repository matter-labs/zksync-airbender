import Airbender.Import.Parse

open Airbender

def main (paths : List String) : IO UInt32 := do
  if paths.isEmpty then
    IO.eprintln "usage: airbender_import <v2 *_layout.json> ..."
    return 2
  let mut failures := 0
  for path in paths do
    try
      match ← loadCircuit path with
      | .error error =>
        IO.eprintln s!"{path}: {error}"
        failures := failures + 1
      | .ok c =>
        let scope := if c.hasReducedLookups then
          "reduced-machine local rows; setup, decoder and global arguments remain external"
          else "local row scope"
        IO.println s!"{path}: OK; Mersenne31; {c.degree_1_constraints.size}/{c.degree_2_constraints.size} linear/quadratic equations, {c.witness_layout.range_check_16_lookup_expressions.size} scalar and {c.witness_layout.timestamp_range_check_lookup_expressions.size} timestamp queries, {c.witness_layout.width_3_lookups.size} native tagged queries; {scope}"
    catch error =>
      IO.eprintln s!"{path}: {error}"
      failures := failures + 1
  return if failures == 0 then 0 else 1
