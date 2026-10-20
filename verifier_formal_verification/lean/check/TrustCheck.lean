import Human.Trust
import Slop.RV.FinalPlain
import Slop.RV.FinalMop
import Slop.Equiv.Decode
import Slop.Equiv.Final
import Slop.Deleg

/-! Run by `verify.sh` (`lake env lean check/TrustCheck.lean`): what `Human/Trust.lean` promises.
1. Every theorem whose statement is a `human/` definition uses only the standard axioms, and its statement mentions
   nothing from `slop/` (or tests).
2. `human/` imports only itself and `Trust.libraries`.
3. Our modules declare no axiom and use no `sorry` or native evaluation; `unsafe`, `partial`, `implemented_by` and
   `extern` occur only in `Trust.tacticModules`. -/

open Lean Elab Command

def stdAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]
def ours (m : Name) : Bool := [`Human, `HumanSail, `Slop, `Image, `ImageMop].any (·.isPrefixOf m)
def inList (m : Name) (l : List Name) : Bool := l.any (·.isPrefixOf m)

elab "#trust_check" : command => do
  let env ← getEnv
  let mods := env.header.moduleNames
  let modOf (n : Name) : Name := match env.getModuleIdxFor? n with
    | some i => mods[i.toNat]!
    | none => .anonymous
  let mut errs : Array String := #[]
  let mut finals : Nat := 0
  -- 1. final theorems
  for (n, ci) in env.constants.map₁.toList do
    let .thmInfo t := ci | continue
    unless (modOf n).getRoot == `Slop do continue
    let .const head _ := t.type.getAppFn | continue
    unless inList (modOf head) Trust.spec && t.type.getAppNumArgs == 0 do continue
    finals := finals + 1
    for c in t.type.getUsedConstants do
      unless inList (modOf c) (Trust.spec ++ Trust.libraries) || !ours (modOf c) do
        errs := errs.push s!"{n}: statement mentions {c} from {modOf c}"
    let axs ← liftCoreM (collectAxioms n)
    for a in axs do
      unless stdAxioms.contains a do errs := errs.push s!"{n}: depends on axiom {a}"
  -- 2. human/ imports
  for i in [:mods.size] do
    let m := mods[i]!
    unless inList m Trust.spec do continue
    for imp in env.header.moduleData[i]!.imports do
      unless inList imp.module (Trust.spec ++ Trust.libraries) do
        errs := errs.push s!"{m} imports {imp.module}, not in Trust.libraries"
  -- 3. escape hatches in our modules
  for (n, ci) in env.constants.map₁.toList do
    let m := modOf n
    unless ours m do continue
    if let .axiomInfo _ := ci then errs := errs.push s!"{n}: axiom declared in {m}"
    let used := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants) |>.getD #[])
    for bad in [``sorryAx, ``Lean.ofReduceBool, ``Lean.ofReduceNat] do
      if used.contains bad then errs := errs.push s!"{n} ({m}) uses {bad}"
    let hatch := ci.isUnsafe
      || (Compiler.implementedByAttr.getParam? env n).isSome || isExtern env n
    if hatch && !inList m Trust.tacticModules then
      errs := errs.push s!"{n}: unsafe/partial/implemented_by/extern outside Trust.tacticModules ({m})"
  if finals == 0 then errs := errs.push "no final theorems found"
  if errs.isEmpty then
    logInfo m!"trust check: OK ({finals} final theorems)"
  else
    throwError m!"trust check failed:\n{String.intercalate "\n" errs.toList}"

#trust_check
