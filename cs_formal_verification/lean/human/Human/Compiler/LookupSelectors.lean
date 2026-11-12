module
public import Human.Helpers.Decoder.RVMachineProgram
public import Human.Compiler.LookupSelectors.AddSub
public import Human.Compiler.LookupSelectors.JumpBranch
public import Human.Compiler.LookupSelectors.MulDiv
public import Human.Compiler.LookupSelectors.ShiftBinop
public import Human.Compiler.LookupSelectors.WordMemory
public import Human.Compiler.LookupSelectors.SubwordMemory
public import Human.Compiler.LookupSelectors.Unified

@[expose] public section
namespace Airbender.Compiler.NativeLookups

/-- Select the actual cached CPU capture. -/
noncomputable def circuitFor : Trace.RVMachineDecoderFamily → Circuit
  | .pooled .addSub => Captures.AddSub.imported.circuit
  | .pooled .jumpBranchSlt => Captures.JumpBranch.imported.circuit
  | .pooled .mulDiv => Captures.MulDiv.imported.circuit
  | .pooled .shiftBinop => Captures.ShiftBinop.imported.circuit
  | .pooled .wordMemory => Captures.WordMemory.imported.circuit
  | .pooled .subwordMemory => Captures.SubwordMemory.imported.circuit
  | .unified => Captures.Unified.imported.circuit

/-- Select every native query operand of that cached CPU. -/
def selectorsFor : Trace.RVMachineDecoderFamily → List Selector
  | .pooled .addSub => addSubSelectors
  | .pooled .jumpBranchSlt => jumpBranchSelectors
  | .pooled .mulDiv => mulDivSelectors
  | .pooled .shiftBinop => shiftBinopSelectors
  | .pooled .wordMemory => wordMemorySelectors
  | .pooled .subwordMemory => subwordMemorySelectors
  | .unified => unifiedSelectors

/-- The selectors cover every actual query operand once, in order. Every cache or copy expansion succeeds. -/
def CachedLookupSelectorsClaim : Prop :=
  ∀ family : Trace.RVMachineDecoderFamily,
    queryLocators (circuitFor family) =
      .ok ((selectorsFor family).map (fun selector => (selector.gate, selector.operand))) ∧
    (selectorsFor family).all (fun selector =>
      match select (circuitFor family) selector with | .ok _ => true | .error _ => false) = true

/-- A cached capture has a nonempty and complete list of resolved native query selectors. -/
def CachedLookupSelectorsSatisfiableClaim : Prop :=
  ∃ family : Trace.RVMachineDecoderFamily,
    selectorsFor family ≠ [] ∧
    queryLocators (circuitFor family) =
      .ok ((selectorsFor family).map (fun selector => (selector.gate, selector.operand))) ∧
    (selectorsFor family).all (fun selector =>
      match select (circuitFor family) selector with | .ok _ => true | .error _ => false) = true

end Airbender.Compiler.NativeLookups
