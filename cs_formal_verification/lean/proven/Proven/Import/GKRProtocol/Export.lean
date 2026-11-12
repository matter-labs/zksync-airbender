module
public meta import Lean

public meta section
set_option warningAsError true

register_option fv.compilerExport : String := { defValue := "", descr := "Copy checked compiler declarations to explicit Lean source." }

namespace Airbender.Compiler.Export
open Lean Elab Command

/-- Record each checked declaration. This option controls only source output. -/
def record (command : Syntax) : CommandElabM Unit := do
  let path : String := fv.compilerExport.get (← getOptions)
  unless path.isEmpty do
    let rendered ← liftCoreM <| PrettyPrinter.ppCategory `command command
    IO.FS.withFile path .append fun handle => handle.putStr ((rendered.pretty.replace "✝" "") ++ "\n\n-- COMPILER_DECL_END\n\n")

/-- Check every declaration unconditionally, then copy its source when requested. -/
def emit (command : Syntax) : CommandElabM Unit := do
  elabCommand command
  if (← get).messages.hasErrors then throwAbortCommand
  record command

end Airbender.Compiler.Export
