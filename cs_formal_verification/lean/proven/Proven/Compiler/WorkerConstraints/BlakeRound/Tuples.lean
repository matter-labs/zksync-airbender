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
public import Mathlib.Tactic.FinCases

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.WorkerConstraints.BlakeRound
open Airbender.Compiler.WorkerConstraints NativeArithmetic NativeWorkerLookups
set_option maxRecDepth 32768

/-- One complete segment of native tuples in selector order. -/
noncomputable def tuple0_000 (physical : GKRAddress → F) : List (List F) := [operand89.input.fields physical, operand90.input.fields physical, operand91.input.fields physical, operand92.input.fields physical, operand93.input.fields physical, operand94.input.fields physical, operand95.input.fields physical, operand96.input.fields physical, operand97.input.fields physical, operand98.input.fields physical, operand99.input.fields physical, operand100.input.fields physical, operand101.input.fields physical, operand102.input.fields physical, operand103.input.fields physical, operand104.input.fields physical]

/-- One complete segment of native tuples in selector order. -/
noncomputable def tuple0_001 (physical : GKRAddress → F) : List (List F) := [operand105.input.fields physical, operand106.input.fields physical, operand107.input.fields physical, operand108.input.fields physical, operand109.input.fields physical, operand110.input.fields physical, operand111.input.fields physical, operand112.input.fields physical, operand113.input.fields physical, operand114.input.fields physical, operand115.input.fields physical, operand116.input.fields physical, operand117.input.fields physical, operand118.input.fields physical, operand119.input.fields physical, operand120.input.fields physical]

/-- One complete segment of native tuples in selector order. -/
noncomputable def tuple0_002 (physical : GKRAddress → F) : List (List F) := [operand121.input.fields physical, operand122.input.fields physical, operand123.input.fields physical, operand124.input.fields physical, operand125.input.fields physical, operand126.input.fields physical, operand127.input.fields physical, operand128.input.fields physical, operand129.input.fields physical, operand130.input.fields physical, operand131.input.fields physical, operand132.input.fields physical, operand133.input.fields physical, operand134.input.fields physical, operand135.input.fields physical, operand136.input.fields physical]

/-- One complete segment of native tuples in selector order. -/
noncomputable def tuple0_003 (physical : GKRAddress → F) : List (List F) := [operand137.input.fields physical, operand138.input.fields physical, operand139.input.fields physical, operand140.input.fields physical, operand141.input.fields physical, operand142.input.fields physical, operand143.input.fields physical, operand144.input.fields physical, operand145.input.fields physical, operand146.input.fields physical, operand147.input.fields physical, operand148.input.fields physical, operand149.input.fields physical, operand150.input.fields physical, operand151.input.fields physical, operand152.input.fields physical]

/-- One complete segment of native tuples in selector order. -/
noncomputable def tuple0_004 (physical : GKRAddress → F) : List (List F) := [operand153.input.fields physical, operand154.input.fields physical, operand155.input.fields physical, operand156.input.fields physical, operand157.input.fields physical, operand158.input.fields physical, operand159.input.fields physical, operand160.input.fields physical, operand161.input.fields physical, operand162.input.fields physical, operand163.input.fields physical, operand164.input.fields physical, operand165.input.fields physical, operand166.input.fields physical, operand167.input.fields physical, operand168.input.fields physical]

/-- One complete segment of native tuples in selector order. -/
noncomputable def tuple0_005 (physical : GKRAddress → F) : List (List F) := [operand169.input.fields physical, operand170.input.fields physical, operand171.input.fields physical, operand172.input.fields physical, operand173.input.fields physical, operand174.input.fields physical, operand175.input.fields physical, operand176.input.fields physical, operand177.input.fields physical, operand178.input.fields physical, operand179.input.fields physical, operand180.input.fields physical, operand181.input.fields physical, operand182.input.fields physical, operand183.input.fields physical, operand184.input.fields physical]

/-- One complete segment of native tuples in selector order. -/
noncomputable def tuple0_006 (physical : GKRAddress → F) : List (List F) := [operand185.input.fields physical, operand186.input.fields physical, operand187.input.fields physical, operand188.input.fields physical, operand189.input.fields physical, operand190.input.fields physical, operand191.input.fields physical, operand192.input.fields physical, operand193.input.fields physical, operand194.input.fields physical, operand195.input.fields physical, operand196.input.fields physical, operand197.input.fields physical, operand198.input.fields physical, operand199.input.fields physical, operand200.input.fields physical]

/-- One complete segment of native tuples in selector order. -/
noncomputable def tuple0_007 (physical : GKRAddress → F) : List (List F) := [operand201.input.fields physical, operand202.input.fields physical, operand203.input.fields physical, operand204.input.fields physical, operand205.input.fields physical, operand206.input.fields physical, operand207.input.fields physical, operand208.input.fields physical, operand209.input.fields physical, operand210.input.fields physical, operand211.input.fields physical, operand212.input.fields physical, operand213.input.fields physical, operand214.input.fields physical, operand215.input.fields physical, operand216.input.fields physical]

/-- One complete segment of native tuples in selector order. -/
noncomputable def tuple0_008 (physical : GKRAddress → F) : List (List F) := [operand217.input.fields physical, operand218.input.fields physical, operand219.input.fields physical, operand220.input.fields physical, operand221.input.fields physical, operand222.input.fields physical, operand223.input.fields physical, operand224.input.fields physical, operand225.input.fields physical, operand226.input.fields physical, operand227.input.fields physical, operand228.input.fields physical, operand229.input.fields physical, operand230.input.fields physical, operand231.input.fields physical, operand232.input.fields physical]

/-- One complete segment of native tuples in selector order. -/
noncomputable def tuple0_009 (physical : GKRAddress → F) : List (List F) := [operand233.input.fields physical, operand234.input.fields physical, operand235.input.fields physical, operand236.input.fields physical, operand237.input.fields physical, operand238.input.fields physical, operand239.input.fields physical, operand240.input.fields physical, operand241.input.fields physical, operand242.input.fields physical, operand243.input.fields physical, operand244.input.fields physical, operand245.input.fields physical, operand246.input.fields physical, operand247.input.fields physical, operand248.input.fields physical]

/-- One complete segment of native tuples in selector order. -/
noncomputable def tuple0_010 (physical : GKRAddress → F) : List (List F) := [operand249.input.fields physical, operand250.input.fields physical, operand251.input.fields physical, operand252.input.fields physical, operand253.input.fields physical, operand254.input.fields physical, operand255.input.fields physical, operand256.input.fields physical, operand257.input.fields physical, operand258.input.fields physical, operand259.input.fields physical, operand260.input.fields physical, operand261.input.fields physical, operand262.input.fields physical, operand263.input.fields physical, operand264.input.fields physical]

/-- One complete segment of native tuples in selector order. -/
noncomputable def tuple0_011 (physical : GKRAddress → F) : List (List F) := [operand265.input.fields physical, operand266.input.fields physical, operand267.input.fields physical, operand268.input.fields physical, operand269.input.fields physical, operand270.input.fields physical, operand271.input.fields physical, operand272.input.fields physical, operand273.input.fields physical, operand274.input.fields physical, operand275.input.fields physical, operand276.input.fields physical, operand277.input.fields physical, operand278.input.fields physical, operand279.input.fields physical, operand280.input.fields physical]

/-- One complete segment of native tuples in selector order. -/
noncomputable def tuple2_000 (physical : GKRAddress → F) : List (List F) := [operand0.input.fields physical, operand1.input.fields physical, operand2.input.fields physical, operand3.input.fields physical, operand4.input.fields physical, operand5.input.fields physical, operand6.input.fields physical, operand7.input.fields physical, operand8.input.fields physical, operand9.input.fields physical, operand10.input.fields physical, operand11.input.fields physical, operand12.input.fields physical, operand13.input.fields physical, operand14.input.fields physical, operand15.input.fields physical]

/-- One complete segment of native tuples in selector order. -/
noncomputable def tuple2_001 (physical : GKRAddress → F) : List (List F) := [operand16.input.fields physical, operand17.input.fields physical, operand18.input.fields physical, operand19.input.fields physical, operand20.input.fields physical, operand21.input.fields physical, operand22.input.fields physical, operand23.input.fields physical, operand24.input.fields physical, operand25.input.fields physical, operand26.input.fields physical, operand27.input.fields physical, operand28.input.fields physical, operand29.input.fields physical, operand30.input.fields physical, operand31.input.fields physical]

/-- One complete segment of native tuples in selector order. -/
noncomputable def tuple2_002 (physical : GKRAddress → F) : List (List F) := [operand32.input.fields physical, operand33.input.fields physical, operand34.input.fields physical, operand35.input.fields physical, operand36.input.fields physical, operand37.input.fields physical, operand38.input.fields physical, operand39.input.fields physical, operand40.input.fields physical, operand41.input.fields physical, operand42.input.fields physical, operand43.input.fields physical, operand44.input.fields physical, operand45.input.fields physical, operand46.input.fields physical, operand47.input.fields physical]

/-- One complete segment of native tuples in selector order. -/
noncomputable def tuple2_003 (physical : GKRAddress → F) : List (List F) := [operand48.input.fields physical, operand49.input.fields physical, operand50.input.fields physical, operand51.input.fields physical, operand52.input.fields physical, operand53.input.fields physical, operand54.input.fields physical, operand55.input.fields physical, operand56.input.fields physical, operand57.input.fields physical, operand58.input.fields physical, operand59.input.fields physical, operand60.input.fields physical, operand61.input.fields physical, operand62.input.fields physical, operand63.input.fields physical]

/-- One complete segment of native tuples in selector order. -/
noncomputable def tuple2_004 (physical : GKRAddress → F) : List (List F) := [operand64.input.fields physical, operand65.input.fields physical, operand66.input.fields physical, operand67.input.fields physical, operand68.input.fields physical, operand69.input.fields physical, operand70.input.fields physical, operand71.input.fields physical, operand72.input.fields physical, operand73.input.fields physical, operand74.input.fields physical, operand75.input.fields physical, operand76.input.fields physical, operand77.input.fields physical, operand78.input.fields physical, operand79.input.fields physical]

/-- One complete segment of native tuples in selector order. -/
noncomputable def tuple2_005 (physical : GKRAddress → F) : List (List F) := [operand80.input.fields physical, operand81.input.fields physical, operand82.input.fields physical, operand83.input.fields physical, operand84.input.fields physical, operand85.input.fields physical, operand86.input.fields physical, operand87.input.fields physical, operand88.input.fields physical]

/-- Every complete native tuple, in the selector order of each group. -/
noncomputable def tuples (physical : GKRAddress → F) (group : Fin 3) : List (List F) :=
  ([(tuple0_000 physical ++ (tuple0_001 physical ++ (tuple0_002 physical ++ (tuple0_003 physical ++ (tuple0_004 physical ++ (tuple0_005 physical ++ (tuple0_006 physical ++ (tuple0_007 physical ++ (tuple0_008 physical ++ (tuple0_009 physical ++ (tuple0_010 physical ++ (tuple0_011 physical ++ [])))))))))))), [], (tuple2_000 physical ++ (tuple2_001 physical ++ (tuple2_002 physical ++ (tuple2_003 physical ++ (tuple2_004 physical ++ (tuple2_005 physical ++ []))))))] : List (List (List F))).get group

/-- The literal tuples are exactly the actual native requests. -/
theorem binding (physical : GKRAddress → F) (group : Fin 3) :
    NativeLookups.requests (circuitFor .blakeRound) (selectorsFor .blakeRound) physical group = .ok (tuples physical group) := by
  fin_cases group <;> kernel_rfl


end Airbender.Compiler.WorkerConstraints.BlakeRound
