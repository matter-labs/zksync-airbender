import Lean
open Lean

private def importsOf (path : System.FilePath) : IO (Array Name) := do
  let text ← IO.FS.readFile path
  let (header, _, messages) ← Parser.parseHeader (Parser.mkInputContext text path.toString)
  if messages.hasErrors then
    throw (IO.userError s!"Cannot parse imports: {path}")
  let mut imports := #[]
  if let `(Parser.Module.header| $[module]? $[prelude]? $items*) := header then
    for item in items do
      if let `(Parser.Module.import| $[public]? $[meta]? import $[all]? $mod) := item then
        imports := imports.push mod.getId
  return imports

def main (args : List String) : IO Unit := do
  let (extra, modules) := match args with
    | "--source-root" :: root :: rest => ([System.FilePath.mk root], rest)
    | _ => ([], args)
  let sp := extra ++ (← getSrcSearchPath)
  let mut pending := modules.toArray.map String.toName
  let mut seen : Std.HashSet Name := {}
  let mut graph := #[]
  while let some current := pending.back? do
    pending := pending.pop
    if seen.contains current then continue
    seen := seen.insert current
    let path ← findLean sp current
    let imports ← importsOf path
    graph := graph.push <| Json.arr #[toJson current.toString, toJson (imports.map Name.toString)]
    pending := pending ++ imports
  IO.println (Json.arr graph).compress
