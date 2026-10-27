import Lake

open Lean System Lake

/-- Recompute Lake's binary-file hash; never trust a cached hash sidecar. -/
def main (args : List String) : IO Unit := do
  let [request] := args | throw (IO.userError "expected a JSON array of compiled-file paths")
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile request))
  let paths ← IO.ofExcept json.getArr?
  for entry in paths do
    let path ← IO.ofExcept entry.getStr?
    let hash ← computeFileHash path
    IO.println (Json.mkObj [("path", toJson path), ("hash", toJson hash.hex)]).compress
