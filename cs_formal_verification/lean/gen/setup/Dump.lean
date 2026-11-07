import Human.Import.SetupEmit
open Airbender.Import.Setup
def gs : GridFn → String
  | .digit d w => s!"(.digit {d} {w})" | .xorDigits a b w => s!"(.xorDigits {a} {b} {w})"
  | .xor4x3 => ".xor4x3" | .rotLow => ".rotLow" | .rotHigh => ".rotHigh" | .xor5 => ".xor5"
  | .chi k => s!"(.chi {k})" | .xorTable w t => s!"(.xorTable {w} TABLE{t.toList})"
def dump (name path : String) : IO Unit := do
  let d ← IO.ofExcept (parseSetup (← IO.FS.readFile path))
  for h : c in [0:d.columns.size] do
    let bs ← IO.ofExcept (structureColumn d.tables c d.columns[c])
    let mut s := 0
    for b in bs do
      let k := match b with
        | .affine n f st => s!"A {n} {f} {st}" | .dense vs => s!"D {vs.size}" | .periodic r st vs => s!"P {r} {st} {vs.size}"
        | .grid n f => s!"G {n} {gs f}"
      IO.println s!"{name} {c} {s} {k}"
      s := s + b.len
#eval dump "blake" "artifacts/setup/blake-round.json"
#eval dump "theta" "artifacts/setup/keccak-theta-rho.json"
#eval dump "parity" "artifacts/setup/keccak-column-parity.json"
#eval dump "chi" "artifacts/setup/keccak-chi5.json"
