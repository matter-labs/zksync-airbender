module
public import Human.Import.Schema

@[expose] public section

namespace Airbender.Compiler

/-- A cached compiled circuit and its public production profile. -/
structure NativeCapture where
  /-- The compiler used cached layers. -/
  cached : Bool
  /-- The complete compiled artifact. -/
  circuit : Circuit
  /-- The exporter selected this circuit family. -/
  family : String
  /-- The exporter format version. -/
  format_version : Nat

end Airbender.Compiler
