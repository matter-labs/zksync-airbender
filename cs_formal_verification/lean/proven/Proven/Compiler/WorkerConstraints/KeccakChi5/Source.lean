module
public import Proven.Compiler.WorkerConstraints.KeccakChi5.Queries000
public import Proven.Compiler.WorkerConstraints.KeccakChi5.Queries001
public import Proven.Compiler.WorkerConstraints.Model

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.KeccakChi5
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- One complete segment of the imported description lookups. -/
noncomputable def queries000 : List (Lookup F) := [sourceLookup18, sourceLookup1, sourceLookup2, sourceLookup3, sourceLookup4, sourceLookup5, sourceLookup6, sourceLookup7, sourceLookup8, sourceLookup9, sourceLookup10, sourceLookup11, sourceLookup12, sourceLookup13, sourceLookup14, sourceLookup15]

/-- One complete segment of the imported description lookups. -/
noncomputable def queries001 : List (Lookup F) := [sourceLookup16, sourceLookup17, sourceLookup0, sourceLookup18]

/-- Every imported lookup, including repeated alignment queries, in source order. -/
noncomputable def sourceQueries : List (Lookup F) :=
  (queries000 ++ (queries001 ++ []))

/-- The checked query list is exactly the full imported worker lookup list. -/
theorem source_binding : FlatOperation.lookups (constraints .chi5) = sourceQueries := by kernel_rfl


end Airbender.Compiler.WorkerConstraints.KeccakChi5
