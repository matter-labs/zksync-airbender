module
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries000
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries001
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries002
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries003
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries004
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries005
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries006
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries007
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries008
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries009
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries010
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries011
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries012
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries013
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries014
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries015
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries016
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries017
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries018
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries019
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries020
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries021
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries022
public import Proven.Compiler.WorkerConstraints.BlakeRound.Queries023
public import Proven.Compiler.WorkerConstraints.Model

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- One complete segment of the imported description lookups. -/
noncomputable def queries000 : List (Lookup F) := [sourceLookup87, sourceLookup88, sourceLookup89, sourceLookup90, sourceLookup91, sourceLookup92, sourceLookup93, sourceLookup94, sourceLookup95, sourceLookup96, sourceLookup97, sourceLookup98, sourceLookup99, sourceLookup100, sourceLookup101, sourceLookup102]

/-- One complete segment of the imported description lookups. -/
noncomputable def queries001 : List (Lookup F) := [sourceLookup103, sourceLookup104, sourceLookup105, sourceLookup106, sourceLookup107, sourceLookup108, sourceLookup109, sourceLookup110, sourceLookup111, sourceLookup112, sourceLookup113, sourceLookup114, sourceLookup115, sourceLookup116, sourceLookup117, sourceLookup118]

/-- One complete segment of the imported description lookups. -/
noncomputable def queries002 : List (Lookup F) := [sourceLookup119, sourceLookup120, sourceLookup121, sourceLookup122, sourceLookup123, sourceLookup124, sourceLookup125, sourceLookup126, sourceLookup127, sourceLookup128, sourceLookup129, sourceLookup130, sourceLookup131, sourceLookup132, sourceLookup133, sourceLookup134]

/-- One complete segment of the imported description lookups. -/
noncomputable def queries003 : List (Lookup F) := [sourceLookup135, sourceLookup136, sourceLookup137, sourceLookup138, sourceLookup139, sourceLookup140, sourceLookup141, sourceLookup142, sourceLookup143, sourceLookup144, sourceLookup145, sourceLookup146, sourceLookup147, sourceLookup148, sourceLookup149, sourceLookup150]

/-- One complete segment of the imported description lookups. -/
noncomputable def queries004 : List (Lookup F) := [sourceLookup151, sourceLookup152, sourceLookup153, sourceLookup154, sourceLookup155, sourceLookup156, sourceLookup157, sourceLookup158, sourceLookup159, sourceLookup160, sourceLookup161, sourceLookup162, sourceLookup163, sourceLookup164, sourceLookup165, sourceLookup166]

/-- One complete segment of the imported description lookups. -/
noncomputable def queries005 : List (Lookup F) := [sourceLookup167, sourceLookup168, sourceLookup169, sourceLookup170, sourceLookup171, sourceLookup172, sourceLookup173, sourceLookup174, sourceLookup175, sourceLookup176, sourceLookup177, sourceLookup178, sourceLookup179, sourceLookup180, sourceLookup181, sourceLookup182]

/-- One complete segment of the imported description lookups. -/
noncomputable def queries006 : List (Lookup F) := [sourceLookup183, sourceLookup184, sourceLookup185, sourceLookup186, sourceLookup187, sourceLookup188, sourceLookup189, sourceLookup190, sourceLookup191, sourceLookup192, sourceLookup193, sourceLookup194, sourceLookup195, sourceLookup196, sourceLookup197, sourceLookup198]

/-- One complete segment of the imported description lookups. -/
noncomputable def queries007 : List (Lookup F) := [sourceLookup199, sourceLookup200, sourceLookup201, sourceLookup202, sourceLookup203, sourceLookup204, sourceLookup205, sourceLookup206, sourceLookup207, sourceLookup208, sourceLookup209, sourceLookup210, sourceLookup211, sourceLookup212, sourceLookup213, sourceLookup214]

/-- One complete segment of the imported description lookups. -/
noncomputable def queries008 : List (Lookup F) := [sourceLookup215, sourceLookup216, sourceLookup217, sourceLookup218, sourceLookup219, sourceLookup220, sourceLookup221, sourceLookup222, sourceLookup223, sourceLookup224, sourceLookup225, sourceLookup226, sourceLookup227, sourceLookup228, sourceLookup229, sourceLookup230]

/-- One complete segment of the imported description lookups. -/
noncomputable def queries009 : List (Lookup F) := [sourceLookup231, sourceLookup232, sourceLookup233, sourceLookup234, sourceLookup235, sourceLookup236, sourceLookup237, sourceLookup238, sourceLookup239, sourceLookup240, sourceLookup241, sourceLookup242, sourceLookup243, sourceLookup244, sourceLookup245, sourceLookup246]

/-- One complete segment of the imported description lookups. -/
noncomputable def queries010 : List (Lookup F) := [sourceLookup247, sourceLookup248, sourceLookup249, sourceLookup250, sourceLookup251, sourceLookup252, sourceLookup253, sourceLookup254, sourceLookup255, sourceLookup256, sourceLookup257, sourceLookup258, sourceLookup259, sourceLookup260, sourceLookup261, sourceLookup262]

/-- One complete segment of the imported description lookups. -/
noncomputable def queries011 : List (Lookup F) := [sourceLookup263, sourceLookup264, sourceLookup265, sourceLookup266, sourceLookup267, sourceLookup268, sourceLookup269, sourceLookup270, sourceLookup271, sourceLookup272, sourceLookup273, sourceLookup274, sourceLookup275, sourceLookup276, sourceLookup277, sourceLookup278]

/-- One complete segment of the imported description lookups. -/
noncomputable def queries012 : List (Lookup F) := [sourceLookup279, sourceLookup280, sourceLookup0, sourceLookup1, sourceLookup2, sourceLookup3, sourceLookup4, sourceLookup5, sourceLookup6, sourceLookup7, sourceLookup8, sourceLookup9, sourceLookup10, sourceLookup11, sourceLookup12, sourceLookup13]

/-- One complete segment of the imported description lookups. -/
noncomputable def queries013 : List (Lookup F) := [sourceLookup14, sourceLookup15, sourceLookup16, sourceLookup17, sourceLookup18, sourceLookup19, sourceLookup20, sourceLookup21, sourceLookup22, sourceLookup23, sourceLookup24, sourceLookup25, sourceLookup26, sourceLookup27, sourceLookup28, sourceLookup29]

/-- One complete segment of the imported description lookups. -/
noncomputable def queries014 : List (Lookup F) := [sourceLookup30, sourceLookup31, sourceLookup32, sourceLookup33, sourceLookup34, sourceLookup35, sourceLookup36, sourceLookup37, sourceLookup38, sourceLookup39, sourceLookup40, sourceLookup41, sourceLookup42, sourceLookup43, sourceLookup44, sourceLookup45]

/-- One complete segment of the imported description lookups. -/
noncomputable def queries015 : List (Lookup F) := [sourceLookup46, sourceLookup47, sourceLookup48, sourceLookup49, sourceLookup50, sourceLookup51, sourceLookup52, sourceLookup53, sourceLookup54, sourceLookup55, sourceLookup56, sourceLookup57, sourceLookup58, sourceLookup59, sourceLookup60, sourceLookup61]

/-- One complete segment of the imported description lookups. -/
noncomputable def queries016 : List (Lookup F) := [sourceLookup62, sourceLookup63, sourceLookup64, sourceLookup65, sourceLookup66, sourceLookup67, sourceLookup68, sourceLookup69, sourceLookup70, sourceLookup71, sourceLookup72, sourceLookup73, sourceLookup74, sourceLookup75, sourceLookup76, sourceLookup77]

/-- One complete segment of the imported description lookups. -/
noncomputable def queries017 : List (Lookup F) := [sourceLookup78, sourceLookup79, sourceLookup80, sourceLookup81, sourceLookup82, sourceLookup83, sourceLookup84, sourceLookup85, sourceLookup86, sourceLookup87, sourceLookup88]

/-- Every imported lookup, including repeated alignment queries, in source order. -/
noncomputable def sourceQueries : List (Lookup F) :=
  (queries000 ++ (queries001 ++ (queries002 ++ (queries003 ++ (queries004 ++ (queries005 ++ (queries006 ++ (queries007 ++ (queries008 ++ (queries009 ++ (queries010 ++ (queries011 ++ (queries012 ++ (queries013 ++ (queries014 ++ (queries015 ++ (queries016 ++ (queries017 ++ []))))))))))))))))))

/-- The checked query list is exactly the full imported worker lookup list. -/
theorem source_binding : FlatOperation.lookups (constraints .blakeRound) = sourceQueries := by kernel_rfl


end Airbender.Compiler.WorkerConstraints.BlakeRound
