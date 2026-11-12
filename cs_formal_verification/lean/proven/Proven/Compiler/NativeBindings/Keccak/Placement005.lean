module
public import Proven.Compiler.NativeBridge
public import Proven.KernelRfl
public import Human.Compiler.Captures.Keccak
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeBindings.Keccak
open Airbender Airbender.Compiler NativeBridge
set_option maxRecDepth 32768

/-- Logical column 120 uses its actual native placement. -/
theorem placement120 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 120 = logical 120 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 120) (by decide)
  have binding : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[120]'(by decide) =
      (120, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 120)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 121 uses its actual native placement. -/
theorem placement121 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 121 = logical 121 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 121) (by decide)
  have binding : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[121]'(by decide) =
      (121, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 121)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 122 uses its actual native placement. -/
theorem placement122 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 122 = logical 122 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 122) (by decide)
  have binding : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[122]'(by decide) =
      (122, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 122)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 123 uses its actual native placement. -/
theorem placement123 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 123 = logical 123 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 123) (by decide)
  have binding : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[123]'(by decide) =
      (123, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 123)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 124 uses its actual native placement. -/
theorem placement124 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 124 = logical 124 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 124) (by decide)
  have binding : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[124]'(by decide) =
      (124, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 124)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 125 uses its actual native placement. -/
theorem placement125 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 125 = logical 125 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 125) (by decide)
  have binding : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[125]'(by decide) =
      (125, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 125)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 126 uses its actual native placement. -/
theorem placement126 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 126 = logical 126 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 126) (by decide)
  have binding : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[126]'(by decide) =
      (126, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 126)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 127 uses its actual native placement. -/
theorem placement127 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 127 = logical 127 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 127) (by decide)
  have binding : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[127]'(by decide) =
      (127, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 127)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 128 uses its actual native placement. -/
theorem placement128 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 128 = logical 128 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 128) (by decide)
  have binding : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[128]'(by decide) =
      (128, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 128)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 129 uses its actual native placement. -/
theorem placement129 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 129 = logical 129 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 129) (by decide)
  have binding : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[129]'(by decide) =
      (129, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 129)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 130 uses its actual native placement. -/
theorem placement130 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 130 = logical 130 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 130) (by decide)
  have binding : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[130]'(by decide) =
      (130, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 130)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 131 uses its actual native placement. -/
theorem placement131 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 131 = logical 131 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 131) (by decide)
  have binding : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[131]'(by decide) =
      (131, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 131)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 132 uses its actual native placement. -/
theorem placement132 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 132 = logical 132 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 132) (by decide)
  have binding : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[132]'(by decide) =
      (132, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 132)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 133 uses its actual native placement. -/
theorem placement133 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 133 = logical 133 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 133) (by decide)
  have binding : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[133]'(by decide) =
      (133, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 133)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 134 uses its actual native placement. -/
theorem placement134 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 134 = logical 134 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 134) (by decide)
  have binding : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[134]'(by decide) =
      (134, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 134)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 135 uses its actual native placement. -/
theorem placement135 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 135 = logical 135 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 135) (by decide)
  have binding : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[135]'(by decide) =
      (135, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 135)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 136 uses its actual native placement. -/
theorem placement136 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 136 = logical 136 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 136) (by decide)
  have binding : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[136]'(by decide) =
      (136, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 136)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 137 uses its actual native placement. -/
theorem placement137 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 137 = logical 137 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 137) (by decide)
  have binding : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[137]'(by decide) =
      (137, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 137)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 138 uses its actual native placement. -/
theorem placement138 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 138 = logical 138 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 138) (by decide)
  have binding : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[138]'(by decide) =
      (138, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 138)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 139 uses its actual native placement. -/
theorem placement139 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 139 = logical 139 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 139) (by decide)
  have binding : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[139]'(by decide) =
      (139, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 139)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 140 uses its actual native placement. -/
theorem placement140 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 140 = logical 140 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 140) (by decide)
  have binding : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[140]'(by decide) =
      (140, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 140)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 141 uses its actual native placement. -/
theorem placement141 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 141 = logical 141 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 141) (by decide)
  have binding : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[141]'(by decide) =
      (141, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 141)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 142 uses its actual native placement. -/
theorem placement142 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 142 = logical 142 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 142) (by decide)
  have binding : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[142]'(by decide) =
      (142, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 142)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 143 uses its actual native placement. -/
theorem placement143 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 143 = logical 143 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 143) (by decide)
  have binding : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[143]'(by decide) =
      (143, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 143)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Public placements cover each column in this batch. -/
theorem placements005 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    ∀ index ∈ [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143],
      (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get index = logical index :=
  (cons_placements (placement120 physical logical agreement) (cons_placements (placement121 physical logical agreement) (cons_placements (placement122 physical logical agreement) (cons_placements (placement123 physical logical agreement) (cons_placements (placement124 physical logical agreement) (cons_placements (placement125 physical logical agreement) (cons_placements (placement126 physical logical agreement) (cons_placements (placement127 physical logical agreement) (cons_placements (placement128 physical logical agreement) (cons_placements (placement129 physical logical agreement) (cons_placements (placement130 physical logical agreement) (cons_placements (placement131 physical logical agreement) (cons_placements (placement132 physical logical agreement) (cons_placements (placement133 physical logical agreement) (cons_placements (placement134 physical logical agreement) (cons_placements (placement135 physical logical agreement) (cons_placements (placement136 physical logical agreement) (cons_placements (placement137 physical logical agreement) (cons_placements (placement138 physical logical agreement) (cons_placements (placement139 physical logical agreement) (cons_placements (placement140 physical logical agreement) (cons_placements (placement141 physical logical agreement) (cons_placements (placement142 physical logical agreement) (cons_placements (placement143 physical logical agreement) (by intro index member; cases member)))))))))))))))))))))))))
end Airbender.Compiler.NativeBindings.Keccak
