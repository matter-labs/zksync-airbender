import Airbender.Import.Parse
import Airbender.Import.Setup

open Airbender

def main (args : List String) : IO UInt32 := do
  if let "--setup" :: paths := args then
    if paths.isEmpty then
      IO.eprintln "usage: airbender_import --setup <setup.json> ..."
      return 2
    let mut failures := 0
    for path in paths do
      try
        match Setup.parse (← IO.FS.readFile path) with
        | .error error =>
          IO.eprintln s!"{path}: {error}"
          failures := failures + 1
        | .ok artifact =>
          IO.println s!"{path}: OK; BabyBear canonical setup; {artifact.trace_len} rows, {artifact.columns.size} columns, {artifact.tables.size} table regions; program inputs: {artifact.program.isSome}"
      catch error =>
        IO.eprintln s!"{path}: {error}"
        failures := failures + 1
    return if failures == 0 then 0 else 1
  if args.isEmpty then
    IO.eprintln "usage: airbender_import <BabyBear *_layout_gkr.json> ..."
    return 2
  let mut failures := 0
  for path in args do
    try
      match ← loadCircuit path with
      | .error err =>
        IO.eprintln s!"{path}: {err}"
        failures := failures + 1
      | .ok c =>
        let gates := c.layers.foldl (fun n l => n + l.gates.size + l.gates_with_external_connections.size) 0
        let caches := c.layers.foldl (fun n l => n + l.cached_relations.size) 0
        IO.println s!"{path}: OK; BabyBear Montgomery; {c.layers.size} layers, {gates} gates, {caches} caches, {c.degree_1_constraints.size}/{c.degree_2_constraints.size} linear/quadratic constraints"
    catch err =>
      IO.eprintln s!"{path}: {err}"
      failures := failures + 1
  return if failures == 0 then 0 else 1
