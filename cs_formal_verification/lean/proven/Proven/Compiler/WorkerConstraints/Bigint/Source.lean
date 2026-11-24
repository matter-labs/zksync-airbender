module
public import Proven.Compiler.WorkerConstraints.Bigint.Queries000
public import Proven.Compiler.WorkerConstraints.Bigint.Queries001
public import Proven.Compiler.WorkerConstraints.Bigint.Queries002
public import Proven.Compiler.WorkerConstraints.Bigint.Queries003
public import Proven.Compiler.WorkerConstraints.Bigint.Queries004
public import Proven.Compiler.WorkerConstraints.Bigint.Queries005
public import Proven.Compiler.WorkerConstraints.Bigint.Queries006
public import Proven.Compiler.WorkerConstraints.Bigint.Queries007
public import Proven.Compiler.WorkerConstraints.Bigint.Queries008
public import Proven.Compiler.WorkerConstraints.Bigint.Queries009
public import Proven.Compiler.WorkerConstraints.Bigint.Queries010
public import Proven.Compiler.WorkerConstraints.Bigint.Queries011
public import Proven.Compiler.WorkerConstraints.Model

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.Bigint
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- One complete segment of the imported description lookups. -/
noncomputable def queries000 : List (Lookup F) := [sourceLookup0, sourceLookup1, sourceLookup2, sourceLookup3, sourceLookup4, sourceLookup5, sourceLookup6, sourceLookup7, sourceLookup8, sourceLookup9, sourceLookup10, sourceLookup11, sourceLookup12, sourceLookup13, sourceLookup14, sourceLookup133]

/-- One complete segment of the imported description lookups. -/
noncomputable def queries001 : List (Lookup F) := [sourceLookup117, sourceLookup118, sourceLookup119, sourceLookup120, sourceLookup121, sourceLookup122, sourceLookup123, sourceLookup124, sourceLookup125, sourceLookup126, sourceLookup127, sourceLookup128, sourceLookup129, sourceLookup130, sourceLookup131, sourceLookup132]

/-- One complete segment of the imported description lookups. -/
noncomputable def queries002 : List (Lookup F) := [sourceLookup54, sourceLookup55, sourceLookup56, sourceLookup57, sourceLookup58, sourceLookup59, sourceLookup60, sourceLookup61, sourceLookup62, sourceLookup63, sourceLookup64, sourceLookup65, sourceLookup66, sourceLookup67, sourceLookup68, sourceLookup69]

/-- One complete segment of the imported description lookups. -/
noncomputable def queries003 : List (Lookup F) := [sourceLookup70, sourceLookup71, sourceLookup72, sourceLookup73, sourceLookup74, sourceLookup75, sourceLookup76, sourceLookup77, sourceLookup78, sourceLookup79, sourceLookup80, sourceLookup81, sourceLookup82, sourceLookup83, sourceLookup84, sourceLookup85]

/-- One complete segment of the imported description lookups. -/
noncomputable def queries004 : List (Lookup F) := [sourceLookup86, sourceLookup87, sourceLookup88, sourceLookup89, sourceLookup90, sourceLookup91, sourceLookup92, sourceLookup93, sourceLookup94, sourceLookup95, sourceLookup96, sourceLookup97, sourceLookup98, sourceLookup99, sourceLookup100, sourceLookup101]

/-- One complete segment of the imported description lookups. -/
noncomputable def queries005 : List (Lookup F) := [sourceLookup102, sourceLookup103, sourceLookup104, sourceLookup105, sourceLookup106, sourceLookup107, sourceLookup108, sourceLookup109, sourceLookup110, sourceLookup111, sourceLookup112, sourceLookup113, sourceLookup114, sourceLookup115, sourceLookup116, sourceLookup15]

/-- One complete segment of the imported description lookups. -/
noncomputable def queries006 : List (Lookup F) := [sourceLookup16, sourceLookup17, sourceLookup18, sourceLookup19, sourceLookup20, sourceLookup21, sourceLookup22, sourceLookup23, sourceLookup24, sourceLookup25, sourceLookup26, sourceLookup27, sourceLookup28, sourceLookup29, sourceLookup30, sourceLookup31]

/-- One complete segment of the imported description lookups. -/
noncomputable def queries007 : List (Lookup F) := [sourceLookup32, sourceLookup33, sourceLookup34, sourceLookup35, sourceLookup36, sourceLookup37, sourceLookup38, sourceLookup39, sourceLookup40, sourceLookup41, sourceLookup42, sourceLookup43, sourceLookup44, sourceLookup45, sourceLookup46, sourceLookup47]

/-- One complete segment of the imported description lookups. -/
noncomputable def queries008 : List (Lookup F) := [sourceLookup48, sourceLookup49, sourceLookup50, sourceLookup51, sourceLookup52, sourceLookup53, sourceLookup54, sourceLookup55]

/-- Every imported lookup, including repeated alignment queries, in source order. -/
noncomputable def sourceQueries : List (Lookup F) :=
  (queries000 ++ (queries001 ++ (queries002 ++ (queries003 ++ (queries004 ++ (queries005 ++ (queries006 ++ (queries007 ++ (queries008 ++ [])))))))))

/-- The checked query list is exactly the full imported worker lookup list. -/
theorem source_binding : FlatOperation.lookups (constraints .bigint) = sourceQueries := by kernel_rfl


end Airbender.Compiler.WorkerConstraints.Bigint
