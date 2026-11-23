module
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Queries000
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Queries001
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Queries002
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Queries003
public import Proven.Compiler.WorkerConstraints.KeccakColumnParity.Queries004
public import Proven.Compiler.WorkerConstraints.Model

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakColumnParity
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- One complete segment of the imported description lookups. -/
noncomputable def queries000 : List (Lookup F) := [sourceLookup50, sourceLookup29, sourceLookup30, sourceLookup31, sourceLookup32, sourceLookup33, sourceLookup34, sourceLookup35, sourceLookup36, sourceLookup37, sourceLookup38, sourceLookup39, sourceLookup40, sourceLookup41, sourceLookup42, sourceLookup43]

/-- One complete segment of the imported description lookups. -/
noncomputable def queries001 : List (Lookup F) := [sourceLookup44, sourceLookup45, sourceLookup46, sourceLookup47, sourceLookup48, sourceLookup49, sourceLookup51, sourceLookup0, sourceLookup1, sourceLookup2, sourceLookup3, sourceLookup4, sourceLookup5, sourceLookup6, sourceLookup7, sourceLookup8]

/-- One complete segment of the imported description lookups. -/
noncomputable def queries002 : List (Lookup F) := [sourceLookup9, sourceLookup10, sourceLookup11, sourceLookup12, sourceLookup13, sourceLookup14, sourceLookup15, sourceLookup16, sourceLookup17, sourceLookup18, sourceLookup19, sourceLookup20, sourceLookup21, sourceLookup22, sourceLookup23, sourceLookup24]

/-- One complete segment of the imported description lookups. -/
noncomputable def queries003 : List (Lookup F) := [sourceLookup25, sourceLookup26, sourceLookup27, sourceLookup28, sourceLookup50]

/-- Every imported lookup, including repeated alignment queries, in source order. -/
noncomputable def sourceQueries : List (Lookup F) :=
  (queries000 ++ (queries001 ++ (queries002 ++ (queries003 ++ []))))

/-- The checked query list is exactly the full imported worker lookup list. -/
theorem source_binding : FlatOperation.lookups (constraints .columnParity) = sourceQueries := by kernel_rfl


end Airbender.Compiler.WorkerConstraints.KeccakColumnParity
