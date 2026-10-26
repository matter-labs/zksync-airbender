import Airbender.Proofs.GKRProtocol.CacheBindings
import Airbender.Import.GKRCompiler.WiringImport

namespace Airbender.Compiler.CacheImport
open Lean Elab Command
set_option warningAsError true

private def constant (value : TSyntax `term) : CommandElabM (TSyntax `term) :=
  `(AffineProgram.constant (Address := GKRAddress) (R := CacheCoefficient) $value)

private def add (left right : TSyntax `term) : CommandElabM (TSyntax `term) :=
  `(AffineProgram.add (Address := GKRAddress) (R := CacheCoefficient) $left $right)

private def scale (coefficient input : TSyntax `term) : CommandElabM (TSyntax `term) :=
  `(AffineProgram.scale (Address := GKRAddress) (R := CacheCoefficient) $coefficient $input)

private def literal (value : Nat) : CommandElabM (TSyntax `term) :=
  `(CacheCoefficient.natural $(quote value))

private def coefficient (value : Coefficient) : CommandElabM (TSyntax `term) :=
  `(CacheCoefficient.base $(quote value.raw.val))

private def memoryInput (offset : Nat) : CommandElabM (TSyntax `term) :=
  `(AffineProgram.input (Address := GKRAddress) (R := CacheCoefficient) (GKRAddress.BaseLayerMemory $(quote offset)))

private def inputSyntax : GKRAddress → CommandElabM (TSyntax `term)
  | .BaseLayerMemory offset => memoryInput offset
  | .BaseLayerWitness offset => `(AffineProgram.input (Address := GKRAddress) (R := CacheCoefficient) (GKRAddress.BaseLayerWitness $(quote offset)))
  | .InnerLayer layer offset => `(AffineProgram.input (Address := GKRAddress) (R := CacheCoefficient) (GKRAddress.InnerLayer $(quote layer) $(quote offset)))
  | .Cached layer offset => `(AffineProgram.input (Address := GKRAddress) (R := CacheCoefficient) (GKRAddress.Cached $(quote layer) $(quote offset)))
  | .Setup offset => `(AffineProgram.input (Address := GKRAddress) (R := CacheCoefficient) (GKRAddress.Setup $(quote offset)))
  | .ScratchSpace _ => throwError "native cache cannot read a ScratchSpace alias"
  | .VirtualSetup kind => do
      let kind ← match kind with
        | .RangeCheck16Bits => `(VirtualSetupPoly.RangeCheck16Bits)
        | .RangeCheckTimestamp => `(VirtualSetupPoly.RangeCheckTimestamp)
        | .InitsAndTeardownsLow => `(VirtualSetupPoly.InitsAndTeardownsLow)
        | .InitsAndTeardownsHigh => `(VirtualSetupPoly.InitsAndTeardownsHigh)
      `(AffineProgram.input (Address := GKRAddress) (R := CacheCoefficient) (GKRAddress.VirtualSetup $kind))

private def linear (row : LinearRelation) : CommandElabM (TSyntax `term) := do
  let mut result ← constant (← coefficient row.constant)
  for (value, address) in row.linear_terms do
    result ← add result (← scale (← coefficient value) (← inputSyntax address))
  return result

private def memoryPower (index : Nat) : CommandElabM (TSyntax `term) :=
  `(CacheCoefficient.memoryPower ⟨$(quote index), by decide⟩)

/-- The same six address/timestamp/value coefficients used by the native
permutation consumer. Address space has coefficient one and gamma is constant.
The unsupported generic-address variant fails closed, as the native helper does. -/
private def memoryTuple (row : SpecialMemoryContributionRelation) :
    CommandElabM (TSyntax `term) := do
  let mut result ← constant (← `(CacheCoefficient.memoryGamma))
  let space ← match row.address_space with
    | .Constant value => constant (← literal value.val)
    | .IsRam offset => memoryInput offset
    | .IsRegister offset => add (← constant (← literal 1)) (← scale (← `(CacheCoefficient.negativeOne)) (← memoryInput offset))
  result ← add result space
  let low ← memoryPower 0
  let high ← memoryPower 1
  match row.address with
  | .ConstantU16 value =>
      result ← add result (← scale low (← constant (← literal value.val)))
  | .Constant value =>
      result ← add result (← scale low (← constant (← literal value.val)))
  | .U16Space offset => result ← add result (← scale low (← memoryInput offset))
  | .U32Space offsets =>
      result ← add result (← scale low (← memoryInput offsets.values[0]!))
      result ← add result (← scale high (← memoryInput offsets.values[1]!))
  | .U32SpaceSpecialIndirect base dynamic offset upper =>
      result ← add result (← scale low (← memoryInput base))
      result ← add result (← scale high (← memoryInput upper))
      if let some (value, address) := dynamic then
        result ← add result (← scale low (← scale (← literal value.val) (← memoryInput address)))
      result ← add result (← scale low (← constant (← literal offset.val)))
  | .U32SpaceGeneric _ => throwError "unsupported native generic memory-cache address"
  match row.timestamp with
  | .Zero => pure ()
  | .Normal offsets =>
      result ← add result (← scale (← memoryPower 2)
        (← add (← memoryInput offsets.values[0]!) (← constant (← literal row.timestamp_offset.val))))
      result ← add result (← scale (← memoryPower 3) (← memoryInput offsets.values[1]!))
  match row.value with
  | .Zero => pure ()
  | .U16Limbs offsets =>
      for index in [:2] do
        result ← add result (← scale (← memoryPower (4 + index)) (← memoryInput offsets.values[index]!))
  | .U8Limbs offsets =>
      for index in [:2] do
        let limb ← add (← memoryInput offsets.values[index * 2]!)
          (← scale (← literal 256) (← memoryInput offsets.values[index * 2 + 1]!))
        result ← add result (← scale (← memoryPower (4 + index)) limb)
  return result

/-- Reflect the actual affine recipe without interpreting challenge values. -/
def program : GKRCacheRelation → CommandElabM (TSyntax `term)
  | .SingleColumnLookup row _ => linear row.input
  | .MemoryTuple row => memoryTuple row
  | .VectorizedLookup row => do
      let mut result ← constant (← `(CacheCoefficient.natural 0))
      for (column, index) in row.columns.toList.zipIdx do
        result ← add result (← scale (← `(CacheCoefficient.lookupPower $(quote index)))
          (← linear column))
      return result
  | .VectorizedLookupSetup addresses => do
      let mut result ← constant (← `(CacheCoefficient.natural 0))
      for (address, index) in addresses.toList.zipIdx do
        result ← add result (← scale (← `(CacheCoefficient.lookupPower $(quote index)))
          (← inputSyntax address))
      return result

private def checksSyntax (proofs : Array (TSyntax `term)) : CommandElabM (TSyntax `term) := do
  let mut result ← `(Compiler.BoolChecks.nil)
  for proof in proofs.reverse do result ← `(Compiler.BoolChecks.cons $proof $result)
  return result

syntax (name := importCacheBindings) "import_cache_bindings " ident " from " str " wiring " ident : command

elab_rules : command
  | `(import_cache_bindings $name:ident from $path:str wiring $wiringName:ident) => do
    let pair ← match Json.parse (← IO.FS.readFile path.getString) >>= (fromJson? (α := Import.Pair)) with
      | .ok pair => pure pair
      | .error error => throwError "invalid compiler artifact for cache semantics: {error}"
    let hom := mkIdent `hom
    let challenges := mkIdent `challenges
    let mut names : Array (TSyntax `term) := #[]
    let mut proofs : Array (TSyntax `term) := #[]
    for layer in pair.circuit.layers do
      for (_, relation) in layer.cached_relations do
        let raw := mkIdent (wiringName.getId ++ Name.mkSimple s!"cache{names.size}")
        let binding := mkIdent (name.getId ++ Name.mkSimple s!"cache{names.size}")
        let recipe := mkIdent (name.getId ++ Name.mkSimple s!"rawCache{names.size}")
        elabCommand (← `(noncomputable def $recipe : CacheBinding CacheCoefficient :=
          ⟨($raw).output, ($raw).inputs, $(← program relation)⟩))
        elabCommand (← `(noncomputable def $binding {R : Type} [CommRing R]
          ($hom : Source.BaseField →+* R) ($challenges : CacheChallenges R) : CacheBinding R :=
          ($recipe).mapCoefficients (CacheCoefficient.value $hom $challenges)))
        names := names.push (← `($recipe))
        let checked := mkIdent (name.getId ++ Name.mkSimple s!"cacheChecked{proofs.size}")
        elabCommand (← `(theorem $checked : ($recipe).portsValid = true := by decide +kernel))
        proofs := proofs.push (← `($checked))
    let rawBindings := mkIdent (name.getId ++ `rawBindings)
    elabCommand (← `(noncomputable def $rawBindings : List (CacheBinding CacheCoefficient) := [$names,*]))
    let rawChecked := mkIdent (name.getId ++ `rawPortsChecked)
    elabCommand (← `(theorem $rawChecked : ($rawBindings).all CacheBinding.portsValid = true :=
      Compiler.BoolChecks.all_true $(← checksSyntax proofs)))
    let bindings := mkIdent (name.getId ++ `bindings)
    elabCommand (← `(noncomputable def $bindings {R : Type} [CommRing R]
      ($hom : Source.BaseField →+* R) ($challenges : CacheChallenges R) : List (CacheBinding R) :=
      ($rawBindings).map (CacheBinding.mapCoefficients (CacheCoefficient.value $hom $challenges))))
    let checked := mkIdent (name.getId ++ `portsChecked)
    elabCommand (← `(theorem $checked {R : Type} [CommRing R]
      ($hom : Source.BaseField →+* R) ($challenges : CacheChallenges R) :
      ($bindings $hom $challenges).all CacheBinding.portsValid = true :=
      CacheBinding.mapCoefficients_all $rawChecked (CacheCoefficient.value $hom $challenges)))
    let graph := mkIdent (wiringName.getId ++ `graph)
    let rawComplete := mkIdent (name.getId ++ `rawComplete)
    elabCommand (← `(theorem $rawComplete :
      ($rawBindings).map (fun cache => (cache.dependencies, cache.output)) =
        ($graph).caches.map (fun cache => (cache.inputs, cache.output)) := by rfl))
    let complete := mkIdent (name.getId ++ `complete)
    elabCommand (← `(theorem $complete {R : Type} [CommRing R]
      ($hom : Source.BaseField →+* R) ($challenges : CacheChallenges R) :
      ($bindings $hom $challenges).map (fun cache => (cache.dependencies, cache.output)) =
        ($graph).caches.map (fun cache => (cache.inputs, cache.output)) :=
      (CacheBinding.mapCoefficients_metadata $rawBindings (CacheCoefficient.value $hom $challenges)).trans $rawComplete))

end Airbender.Compiler.CacheImport
