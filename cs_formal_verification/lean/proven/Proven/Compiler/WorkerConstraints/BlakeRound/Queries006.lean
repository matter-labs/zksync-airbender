module
public import Proven.Compiler.WorkerConstraints.Values
public import Proven.Compiler.WorkerConstraints.Setup
public import Proven.KernelRfl

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- One actual resolved primitive operand. -/
noncomputable def operand72 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 224)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 189)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 528))], ⟨⟨133099247, by decide⟩⟩⟩, 72⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions72 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 738]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 739])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup72 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions72⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields72 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 738]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 739])])).eval (Verification.environment logical)]

theorem source_values72 (logical : Nat → F) :
    (sourceExpressions72.map (Verification.environment logical)).toList = sourceFields72 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics72 (logical : Nat → F) :
    (sourceLookup72).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields72 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup72, sourceExpressions72, sourceFields72, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 738]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 739])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand73 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 223)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 192)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 529))], ⟨⟨1476395013, by decide⟩⟩⟩, 73⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions73 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 740]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 742])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup73 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions73⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields73 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 740]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 742])])).eval (Verification.environment logical)]

theorem source_values73 (logical : Nat → F) :
    (sourceExpressions73.map (Verification.environment logical)).toList = sourceFields73 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics73 (logical : Nat → F) :
    (sourceLookup73).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields73 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup73, sourceExpressions73, sourceFields73, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 740]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 742])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand74 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 224)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 193)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 529))], ⟨⟨133099247, by decide⟩⟩⟩, 74⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions74 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 741]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 742])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup74 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions74⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields74 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 741]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 742])])).eval (Verification.environment logical)]

theorem source_values74 (logical : Nat → F) :
    (sourceExpressions74.map (Verification.environment logical)).toList = sourceFields74 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics74 (logical : Nat → F) :
    (sourceLookup74).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields74 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup74, sourceExpressions74, sourceFields74, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 741]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 742])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand75 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 223)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 196)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 530))], ⟨⟨1476395013, by decide⟩⟩⟩, 75⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions75 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 743]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 745])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup75 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions75⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields75 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 743]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 745])])).eval (Verification.environment logical)]

theorem source_values75 (logical : Nat → F) :
    (sourceExpressions75.map (Verification.environment logical)).toList = sourceFields75 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics75 (logical : Nat → F) :
    (sourceLookup75).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields75 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup75, sourceExpressions75, sourceFields75, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 743]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 745])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand76 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 224)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 197)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 530))], ⟨⟨133099247, by decide⟩⟩⟩, 76⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions76 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 744]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 745])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup76 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions76⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields76 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 744]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 745])])).eval (Verification.environment logical)]

theorem source_values76 (logical : Nat → F) :
    (sourceExpressions76.map (Verification.environment logical)).toList = sourceFields76 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics76 (logical : Nat → F) :
    (sourceLookup76).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields76 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup76, sourceExpressions76, sourceFields76, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 744]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 745])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand77 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 223)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 200)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 531))], ⟨⟨1476395013, by decide⟩⟩⟩, 77⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions77 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 746]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 748])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup77 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions77⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields77 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 746]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 748])])).eval (Verification.environment logical)]

theorem source_values77 (logical : Nat → F) :
    (sourceExpressions77.map (Verification.environment logical)).toList = sourceFields77 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics77 (logical : Nat → F) :
    (sourceLookup77).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields77 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup77, sourceExpressions77, sourceFields77, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 746]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 748])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand78 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 224)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 201)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 531))], ⟨⟨133099247, by decide⟩⟩⟩, 78⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions78 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 747]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 748])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup78 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions78⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields78 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 747]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 748])])).eval (Verification.environment logical)]

theorem source_values78 (logical : Nat → F) :
    (sourceExpressions78.map (Verification.environment logical)).toList = sourceFields78 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics78 (logical : Nat → F) :
    (sourceLookup78).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields78 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup78, sourceExpressions78, sourceFields78, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 747]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 748])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand79 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 223)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 204)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 532))], ⟨⟨1476395013, by decide⟩⟩⟩, 79⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions79 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 749]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 751])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup79 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions79⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields79 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 749]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 751])])).eval (Verification.environment logical)]

theorem source_values79 (logical : Nat → F) :
    (sourceExpressions79.map (Verification.environment logical)).toList = sourceFields79 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics79 (logical : Nat → F) :
    (sourceLookup79).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields79 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup79, sourceExpressions79, sourceFields79, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 749]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 751])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand80 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 224)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 205)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 532))], ⟨⟨133099247, by decide⟩⟩⟩, 80⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions80 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 750]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 751])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup80 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions80⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields80 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 750]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 751])])).eval (Verification.environment logical)]

theorem source_values80 (logical : Nat → F) :
    (sourceExpressions80.map (Verification.environment logical)).toList = sourceFields80 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics80 (logical : Nat → F) :
    (sourceLookup80).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields80 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup80, sourceExpressions80, sourceFields80, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 750]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 751])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand81 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 223)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 208)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 533))], ⟨⟨1476395013, by decide⟩⟩⟩, 81⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions81 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 752]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 754])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup81 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions81⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields81 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 752]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 754])])).eval (Verification.environment logical)]

theorem source_values81 (logical : Nat → F) :
    (sourceExpressions81.map (Verification.environment logical)).toList = sourceFields81 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics81 (logical : Nat → F) :
    (sourceLookup81).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields81 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup81, sourceExpressions81, sourceFields81, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 752]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 754])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand82 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 224)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 209)), (⟨⟨1744830467, by decide⟩⟩, (.BaseLayerWitness 533))], ⟨⟨133099247, by decide⟩⟩⟩, 82⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions82 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 753]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 754])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup82 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions82⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields82 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 753]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 754])])).eval (Verification.environment logical)]

theorem source_values82 (logical : Nat → F) :
    (sourceExpressions82.map (Verification.environment logical)).toList = sourceFields82 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics82 (logical : Nat → F) :
    (sourceLookup82).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields82 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup82, sourceExpressions82, sourceFields82, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨133099247, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 2]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 753]), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 754])])) logical

/-- One actual resolved primitive operand. -/
noncomputable def operand83 : NativeLookups.Operand := ⟨.one, .scalar ⟨⟨#[(⟨⟨1744830467, by decide⟩⟩, (.BaseLayerMemory 223)), (⟨⟨268435454, by decide⟩⟩, (.BaseLayerMemory 212)), (⟨⟨133099247, by decide⟩⟩, (.BaseLayerWitness 534))], ⟨⟨1476395013, by decide⟩⟩⟩, 83⟩⟩

/-- The retained logical expressions of the same query. -/
noncomputable def sourceExpressions83 : Vector (Airbender.Expression F) 1 := #v[Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 755]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 757])])]

/-- The query uses its reviewed source table. -/
noncomputable def sourceLookup83 : Lookup F := ⟨(Trace.timestampTable).toRaw, sourceExpressions83⟩

/-- Evaluated source fields retain their complete order. -/
noncomputable def sourceFields83 (logical : Nat → F) : List F := [(Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 755]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 757])])).eval (Verification.environment logical)]

theorem source_values83 (logical : Nat → F) :
    (sourceExpressions83.map (Verification.environment logical)).toList = sourceFields83 logical := by kernel_rfl

/-- The reviewed scalar query and public native range have the same members. -/
theorem source_semantics83 (logical : Nat → F) :
    (sourceLookup83).Contains (Verification.environment logical) ↔
      ∃ index, sourceFields83 logical = NativeWorkerSetup.rows .blakeRound 2 index := by
  simpa only [sourceLookup83, sourceExpressions83, sourceFields83, Trace.timestampLookup] using
    timestamp_refinement .blakeRound (Import.expression (.Sum #[(.Constant ⟨⟨1476395013, by decide⟩⟩), (.Product #[.Constant ⟨⟨1744830467, by decide⟩⟩, .Var 1]), (.Product #[.Constant ⟨⟨268435454, by decide⟩⟩, .Var 755]), (.Product #[.Constant ⟨⟨133099247, by decide⟩⟩, .Var 757])])) logical


end Airbender.Compiler.WorkerConstraints.BlakeRound
