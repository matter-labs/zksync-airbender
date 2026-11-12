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

/-- Logical column 144 uses its actual native placement. -/
theorem placement144 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 144 = logical 144 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 144) (by decide)
  have binding : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[144]'(by decide) =
      (144, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 144)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 145 uses its actual native placement. -/
theorem placement145 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 145 = logical 145 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 145) (by decide)
  have binding : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[145]'(by decide) =
      (145, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 145)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 146 uses its actual native placement. -/
theorem placement146 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 146 = logical 146 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 146) (by decide)
  have binding : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[146]'(by decide) =
      (146, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 146)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 147 uses its actual native placement. -/
theorem placement147 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 147 = logical 147 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 147) (by decide)
  have binding : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[147]'(by decide) =
      (147, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 147)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 148 uses its actual native placement. -/
theorem placement148 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 148 = logical 148 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 148) (by decide)
  have binding : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[148]'(by decide) =
      (148, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 148)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 149 uses its actual native placement. -/
theorem placement149 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 149 = logical 149 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 149) (by decide)
  have binding : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[149]'(by decide) =
      (149, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 149)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 150 uses its actual native placement. -/
theorem placement150 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 150 = logical 150 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 150) (by decide)
  have binding : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[150]'(by decide) =
      (150, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 150)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 151 uses its actual native placement. -/
theorem placement151 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 151 = logical 151 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 151) (by decide)
  have binding : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[151]'(by decide) =
      (151, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 151)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 152 uses its actual native placement. -/
theorem placement152 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 152 = logical 152 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 152) (by decide)
  have binding : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[152]'(by decide) =
      (152, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 152)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 153 uses its actual native placement. -/
theorem placement153 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 153 = logical 153 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 153) (by decide)
  have binding : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[153]'(by decide) =
      (153, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 153)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 154 uses its actual native placement. -/
theorem placement154 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 154 = logical 154 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 154) (by decide)
  have binding : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[154]'(by decide) =
      (154, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 154)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 155 uses its actual native placement. -/
theorem placement155 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 155 = logical 155 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 155) (by decide)
  have binding : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[155]'(by decide) =
      (155, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 155)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 156 uses its actual native placement. -/
theorem placement156 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 156 = logical 156 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 156) (by decide)
  have binding : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[156]'(by decide) =
      (156, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 156)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 157 uses its actual native placement. -/
theorem placement157 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 157 = logical 157 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 157) (by decide)
  have binding : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[157]'(by decide) =
      (157, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 157)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 158 uses its actual native placement. -/
theorem placement158 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 158 = logical 158 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 158) (by decide)
  have binding : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[158]'(by decide) =
      (158, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 158)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 159 uses its actual native placement. -/
theorem placement159 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 159 = logical 159 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 159) (by decide)
  have binding : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[159]'(by decide) =
      (159, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 159)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 160 uses its actual native placement. -/
theorem placement160 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 160 = logical 160 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 160) (by decide)
  have binding : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[160]'(by decide) =
      (160, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 160)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 161 uses its actual native placement. -/
theorem placement161 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 161 = logical 161 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 161) (by decide)
  have binding : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[161]'(by decide) =
      (161, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 161)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 162 uses its actual native placement. -/
theorem placement162 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 162 = logical 162 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 162) (by decide)
  have binding : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[162]'(by decide) =
      (162, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 162)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 163 uses its actual native placement. -/
theorem placement163 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 163 = logical 163 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 163) (by decide)
  have binding : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[163]'(by decide) =
      (163, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 163)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 164 uses its actual native placement. -/
theorem placement164 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 164 = logical 164 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 164) (by decide)
  have binding : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[164]'(by decide) =
      (164, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 164)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 165 uses its actual native placement. -/
theorem placement165 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 165 = logical 165 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 165) (by decide)
  have binding : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[165]'(by decide) =
      (165, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 165)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 166 uses its actual native placement. -/
theorem placement166 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 166 = logical 166 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 166) (by decide)
  have binding : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[166]'(by decide) =
      (166, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 166)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Logical column 167 uses its actual native placement. -/
theorem placement167 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get 167 = logical 167 := by
  have included := Array.getElem_mem (xs := (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries) (i := 167) (by decide)
  have binding : (Airbender.Compiler.Captures.Keccak.imported.circuit).placement_data.entries[167]'(by decide) =
      (167, Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.placement 167)) := by kernel_rfl
  exact (congrArg physical (congrArg Prod.snd binding)).symm.trans
    ((agreement _ included).symm.trans (congrArg logical (congrArg Prod.fst binding)))

/-- Public placements cover each column in this batch. -/
theorem placements006 (physical : GKRAddress → NativeArithmetic.F) (logical : Nat → NativeArithmetic.F)
    (agreement : NativeArithmetic.PlacementAgreement Airbender.Compiler.Captures.Keccak.imported.circuit physical logical) :
    ∀ index ∈ [144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167],
      (Airbender.Compiler.CleanArithmeticNative.KeccakCached.native.environment physical (Verification.environment logical).data).get index = logical index :=
  (cons_placements (placement144 physical logical agreement) (cons_placements (placement145 physical logical agreement) (cons_placements (placement146 physical logical agreement) (cons_placements (placement147 physical logical agreement) (cons_placements (placement148 physical logical agreement) (cons_placements (placement149 physical logical agreement) (cons_placements (placement150 physical logical agreement) (cons_placements (placement151 physical logical agreement) (cons_placements (placement152 physical logical agreement) (cons_placements (placement153 physical logical agreement) (cons_placements (placement154 physical logical agreement) (cons_placements (placement155 physical logical agreement) (cons_placements (placement156 physical logical agreement) (cons_placements (placement157 physical logical agreement) (cons_placements (placement158 physical logical agreement) (cons_placements (placement159 physical logical agreement) (cons_placements (placement160 physical logical agreement) (cons_placements (placement161 physical logical agreement) (cons_placements (placement162 physical logical agreement) (cons_placements (placement163 physical logical agreement) (cons_placements (placement164 physical logical agreement) (cons_placements (placement165 physical logical agreement) (cons_placements (placement166 physical logical agreement) (cons_placements (placement167 physical logical agreement) (by intro index member; cases member)))))))))))))))))))))))))
end Airbender.Compiler.NativeBindings.Keccak
