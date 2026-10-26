import Airbender.Proofs.GKRProtocol.FunctionalReplacement
import Airbender.Import.GKRProtocol.NativeProductImport

namespace Airbender.Compiler.InitializationWindowImport
open Lean Elab Command
set_option warningAsError true

private def emitChecked (command : Syntax) : CommandElabM Unit := do
  withEnableInfoTree false (elabCommand command)
  if (← get).messages.hasErrors then throwAbortCommand

private def addressSyntax : GKRAddress → CommandElabM (TSyntax `term)
  | .BaseLayerMemory index => `(GKRAddress.BaseLayerMemory $(quote index))
  | .InnerLayer layer offset => `(GKRAddress.InnerLayer $(quote layer) $(quote offset))
  | .VirtualSetup .InitsAndTeardownsLow => `(GKRAddress.VirtualSetup .InitsAndTeardownsLow)
  | .VirtualSetup .InitsAndTeardownsHigh => `(GKRAddress.VirtualSetup .InitsAndTeardownsHigh)
  | _ => throwError "unsupported initialization boundary address"

private def payload (circuit : Circuit) (state : InitsOrTeardownsTimestampAndValue)
    (setup : Fixed 2 GKRAddress) (setIndex side : Nat) : CommandElabM (TSyntax `term) := do
  let some bits := circuit.memory_layout.inits_and_teardowns_word_bits | throwError "missing initialization word width"
  let log := Nat.log2 circuit.trace_len
  unless bits.val == 2 && 2 ^ log == circuit.trace_len && 16 ≤ log + bits.val do
    throwError "unsupported native initialization geometry"
  let [low, high] := setup.values.toList | throwError "incorrect initialization setup width"
  let stride := 2 ^ (log + bits.val - 16)
  let input (address : GKRAddress) : CommandElabM (TSyntax `term) := do
    `(AffineProgram.input (R := CacheCoefficient) $(← addressSyntax address))
  let scaled (index : Nat) (entry : TSyntax `term) : CommandElabM (TSyntax `term) :=
    `(AffineProgram.scale (CacheCoefficient.memoryPower ⟨$(quote index), by decide⟩) $entry)
  let mut result ← `(AffineProgram.add (AffineProgram.constant (Address := GKRAddress) CacheCoefficient.memoryGamma)
    (AffineProgram.constant (CacheCoefficient.natural 1)))
  result ← `(AffineProgram.add $result $(← scaled 0 (← input low)))
  let highInput ← `(AffineProgram.add $(← input high)
    (AffineProgram.constant (CacheCoefficient.natural ((publicTops $(quote setIndex)) * $(quote stride)))))
  result ← `(AffineProgram.add $result $(← scaled 1 highInput))
  match state with
  | .Init => pure ()
  | .Teardown leftTimestamp leftValue rightTimestamp rightValue =>
    let timestamps := if side == 0 then leftTimestamp else rightTimestamp
    let values := if side == 0 then leftValue else rightValue
    for (column, index) in (timestamps.values ++ values.values).toList.zipIdx do
      result ← `(AffineProgram.add $result $(← scaled (index + 2) (← input (.BaseLayerMemory column))))
  return result

/-- Retain the public per-set top-bit argument used by Rust's forward loop.
The artifact supplies set selectors, scalar columns, setup ports and outputs. -/
elab "import_initialization_windows " name:ident " from " path:str : command => do
  let pair ← match Json.parse (← IO.FS.readFile path.getString) >>= (fromJson? (α := Import.Pair)) with
    | .ok pair => pure pair | .error error => throwError "{error}"
  let mut ordinal := 0
  for layer in pair.circuit.layers do
    for gate in layer.gates ++ layer.gates_with_external_connections do
      if let .InitsOrTeardownsInitialPair state setup output sets := gate.enforced_relation then
        let [left, right] := sets.values.toList | throwError "incorrect initialization set pair"
        let leftTerm ← payload pair.circuit state setup left 0
        let rightTerm ← payload pair.circuit state setup right 1
        let gateName := mkIdent (name.getId.appendAfter s!"Gate{ordinal}")
        emitChecked (← `(noncomputable def $gateName (publicTops : Nat → Nat) : NativeProductGate :=
          .pair $(← addressSyntax output) $leftTerm $rightTerm))
        ordinal := ordinal + 1
  unless ordinal == 2 do throwError "expected exactly one inline init/teardown pair"

end Airbender.Compiler.InitializationWindowImport
