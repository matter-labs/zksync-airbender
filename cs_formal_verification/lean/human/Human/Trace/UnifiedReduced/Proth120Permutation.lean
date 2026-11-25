module
public import Human.Compiler.NativeMemory
public import Human.Trace.UnifiedReduced.Proth120Trace

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120
open Trace Compiler.NativeMemory

/-- One permutation over the wrap's native PC, register and RAM tokens, grouped by port. -/
def WrapPermutation (t : WrapTrace) : Prop :=
  (((t.initial :: t.rows.map Row.finish).map stateToken) ++ t.initialMemory ++ t.rows.flatMap Row.writes).Perm
    (((t.terminal :: t.rows.map Row.start).map stateToken) ++ t.terminalMemory ++ t.rows.flatMap Row.reads)

end Airbender.UnifiedReduced.Proth120
