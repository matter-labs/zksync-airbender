module
public import Human.Compiler.LookupSelectors.Workers.Bigint
public import Human.Compiler.LookupSelectors.Workers.BlakeG
public import Human.Compiler.LookupSelectors.Workers.BlakeRound
public import Human.Compiler.LookupSelectors.Workers.KeccakColumnParity
public import Human.Compiler.LookupSelectors.Workers.KeccakThetaRho
public import Human.Compiler.LookupSelectors.Workers.KeccakChi5

@[expose] public section
namespace Airbender.Compiler.NativeWorkerLookups

/-- The cached worker circuits used by the native machine targets. -/
inductive Family where
  | bigint | blakeG | blakeRound | columnParity | thetaRho | chi5
  deriving DecidableEq

/-- The production cached capture for each worker. -/
noncomputable def circuitFor : Family → Circuit
  | .bigint => Captures.Bigint.imported.circuit
  | .blakeG => Captures.BlakeG.imported.circuit
  | .blakeRound => Captures.BlakeRound.imported.circuit
  | .columnParity => Captures.KeccakColumnParity.imported.circuit
  | .thetaRho => Captures.KeccakThetaRho.imported.circuit
  | .chi5 => Captures.KeccakChi5.imported.circuit

/-- Every actual native query operand of the worker. -/
def selectorsFor : Family → List NativeLookups.Selector
  | .bigint => bigintSelectors
  | .blakeG => blakeGSelectors
  | .blakeRound => blakeRoundSelectors
  | .columnParity => keccakColumnParitySelectors
  | .thetaRho => keccakThetaRhoSelectors
  | .chi5 => keccakChi5Selectors

/-- The worker selectors cover every query once, resolve its payload and use its native chain group.
    The table side of each lookup group reads the setup columns of `NativeLookups.tableOperand`. -/
def CachedWorkerLookupSelectorsClaim : Prop :=
  ∀ family : Family,
    NativeLookups.queryLocators (circuitFor family) =
      .ok ((selectorsFor family).map (fun selector => (selector.gate, selector.operand))) ∧
    (selectorsFor family).all (fun selector =>
      match NativeLookups.select (circuitFor family) selector with
      | .ok _ => true | .error _ => false) = true ∧
    NativeLookups.groupsAgree (circuitFor family) (selectorsFor family) = true ∧
    NativeLookups.TableSidesRead (circuitFor family)

/-- A cached worker has a nonempty query list with all selector conditions and its table sides. -/
def CachedWorkerLookupSelectorsSatisfiableClaim : Prop :=
  ∃ family : Family, selectorsFor family ≠ [] ∧
    NativeLookups.queryLocators (circuitFor family) =
      .ok ((selectorsFor family).map (fun selector => (selector.gate, selector.operand))) ∧
    (selectorsFor family).all (fun selector =>
      match NativeLookups.select (circuitFor family) selector with
      | .ok _ => true | .error _ => false) = true ∧
    NativeLookups.groupsAgree (circuitFor family) (selectorsFor family) = true ∧
    NativeLookups.TableSidesRead (circuitFor family)

end Airbender.Compiler.NativeWorkerLookups
