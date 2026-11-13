module
public meta import Proven.GKRProtocol.Source
public meta import Human.Import.CompilerJson
public meta import Lean

public meta section
set_option warningAsError true
namespace Airbender.Compiler.Source
open Lean
deriving instance FromJson for Table
deriving instance FromJson for LookupInput
deriving instance FromJson for LookupTable
deriving instance FromJson for Lookup
deriving instance FromJson for RangeCheck
deriving instance FromJson for CycleState
deriving instance FromJson for Decoder
deriving instance FromJson for Executor
deriving instance FromJson for Delegation
deriving instance FromJson for Boolean
deriving instance FromJson for ConstantRegisterAccess
deriving instance FromJson for RegisterAccess
deriving instance FromJson for RegisterOrRamAccess
deriving instance FromJson for IndirectRamAccess
deriving instance FromJson for MemoryAccess
deriving instance FromJson for RegisterMode
deriving instance FromJson for IndirectMode
deriving instance FromJson for RegisterAndIndirectAccess
deriving instance FromJson for SemanticInputs
deriving instance FromJson for Configuration
deriving instance FromJson for Snapshot
end Airbender.Compiler.Source
