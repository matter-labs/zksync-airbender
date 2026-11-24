module
public import Proven.Compiler.Lookups.NativeRanges
public import Proven.Compiler.Lookups.Source.AddSub
public import Proven.Compiler.NativeBindings.AddSub
public import Proven.Compiler.Lookups.Source.JumpBranch
public import Proven.Compiler.NativeBindings.JumpBranch
public import Proven.Compiler.Lookups.Source.MulDiv
public import Proven.Compiler.NativeBindings.MulDiv
public import Proven.Compiler.Lookups.Source.ShiftBinop
public import Proven.Compiler.NativeBindings.ShiftBinop
public import Proven.Compiler.Lookups.Source.WordMemory
public import Proven.Compiler.NativeBindings.WordMemory
public import Proven.Compiler.Lookups.Source.SubwordMemory
public import Proven.Compiler.NativeBindings.SubwordMemory
public import Proven.Compiler.Lookups.Source.Unified
public import Proven.Compiler.NativeBindings.Unified

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeHelpers.AddSub
open Airbender Airbender.Compiler Airbender.Trace NativeArithmetic

/-- Exact native timestamp matching bounds every physical helper value. -/
theorem bounded (initial : RV.State) (program : List RVMachineProgramEntry)
    (physical : GKRAddress → F)
    (accepted : Holds (NativeLookups.circuitFor (.pooled .addSub)) physical)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .addSub))
      (NativeLookups.selectorsFor (.pooled .addSub)) physical (NativePublicSetup.rows initial program (.pooled .addSub))) :
    ∀ field ∈ Airbender.Compiler.HelperNative.AddSubCached.native.fields,
      (field.value (Airbender.Compiler.HelperNative.AddSubCached.native.sourceValues physical)).val < 524288 := by
  intro field member
  let value := field.value (Airbender.Compiler.HelperNative.AddSubCached.native.sourceValues physical)
  have present := NativeSourceTransport.AddSub.source_member
    (NativeBindings.AddSub.scalar_gates physical accepted) arguments 2 (MaterializedQuery.mk [value] 1)
    (by simpa [NativeSourceTransport.AddSub.sourceRequests, value,
          Airbender.Compiler.HelperNative.AddSubCached.native.sourceValues] using
        (List.mem_map.mpr ⟨field, member, rfl⟩ :
          MaterializedQuery.mk [field.value (Airbender.Compiler.HelperNative.AddSubCached.native.sourceValues physical)] 1 ∈
            Airbender.Compiler.HelperNative.AddSubCached.native.fields.map (fun item => MaterializedQuery.mk
              [item.value (Airbender.Compiler.HelperNative.AddSubCached.native.sourceValues physical)] 1))) one_ne_zero
  obtain ⟨index, same⟩ := present
  exact NativePublicSetup.Proofs.timestamp_bound same

end Airbender.Compiler.NativeHelpers.AddSub

namespace Airbender.Compiler.NativeHelpers.JumpBranch
open Airbender Airbender.Compiler Airbender.Trace NativeArithmetic

/-- Exact native timestamp matching bounds every physical helper value. -/
theorem bounded (initial : RV.State) (program : List RVMachineProgramEntry)
    (physical : GKRAddress → F)
    (accepted : Holds (NativeLookups.circuitFor (.pooled .jumpBranchSlt)) physical)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .jumpBranchSlt))
      (NativeLookups.selectorsFor (.pooled .jumpBranchSlt)) physical (NativePublicSetup.rows initial program (.pooled .jumpBranchSlt))) :
    ∀ field ∈ Airbender.Compiler.HelperNative.JumpBranchCached.native.fields,
      (field.value (Airbender.Compiler.HelperNative.JumpBranchCached.native.sourceValues physical)).val < 524288 := by
  intro field member
  let value := field.value (Airbender.Compiler.HelperNative.JumpBranchCached.native.sourceValues physical)
  have present := NativeSourceTransport.JumpBranch.source_member
    (NativeBindings.JumpBranch.scalar_gates physical accepted) arguments 2 (MaterializedQuery.mk [value] 1)
    (by simpa [NativeSourceTransport.JumpBranch.sourceRequests, value,
          Airbender.Compiler.HelperNative.JumpBranchCached.native.sourceValues] using
        (List.mem_map.mpr ⟨field, member, rfl⟩ :
          MaterializedQuery.mk [field.value (Airbender.Compiler.HelperNative.JumpBranchCached.native.sourceValues physical)] 1 ∈
            Airbender.Compiler.HelperNative.JumpBranchCached.native.fields.map (fun item => MaterializedQuery.mk
              [item.value (Airbender.Compiler.HelperNative.JumpBranchCached.native.sourceValues physical)] 1))) one_ne_zero
  obtain ⟨index, same⟩ := present
  exact NativePublicSetup.Proofs.timestamp_bound same

end Airbender.Compiler.NativeHelpers.JumpBranch

namespace Airbender.Compiler.NativeHelpers.MulDiv
open Airbender Airbender.Compiler Airbender.Trace NativeArithmetic

/-- Exact native timestamp matching bounds every physical helper value. -/
theorem bounded (initial : RV.State) (program : List RVMachineProgramEntry)
    (physical : GKRAddress → F)
    (accepted : Holds (NativeLookups.circuitFor (.pooled .mulDiv)) physical)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .mulDiv))
      (NativeLookups.selectorsFor (.pooled .mulDiv)) physical (NativePublicSetup.rows initial program (.pooled .mulDiv))) :
    ∀ field ∈ Airbender.Compiler.HelperNative.MulDivCached.native.fields,
      (field.value (Airbender.Compiler.HelperNative.MulDivCached.native.sourceValues physical)).val < 524288 := by
  intro field member
  let value := field.value (Airbender.Compiler.HelperNative.MulDivCached.native.sourceValues physical)
  have present := NativeSourceTransport.MulDiv.source_member
    (NativeBindings.MulDiv.scalar_gates physical accepted) arguments 2 (MaterializedQuery.mk [value] 1)
    (by simpa [NativeSourceTransport.MulDiv.sourceRequests, value,
          Airbender.Compiler.HelperNative.MulDivCached.native.sourceValues] using
        (List.mem_map.mpr ⟨field, member, rfl⟩ :
          MaterializedQuery.mk [field.value (Airbender.Compiler.HelperNative.MulDivCached.native.sourceValues physical)] 1 ∈
            Airbender.Compiler.HelperNative.MulDivCached.native.fields.map (fun item => MaterializedQuery.mk
              [item.value (Airbender.Compiler.HelperNative.MulDivCached.native.sourceValues physical)] 1))) one_ne_zero
  obtain ⟨index, same⟩ := present
  exact NativePublicSetup.Proofs.timestamp_bound same

end Airbender.Compiler.NativeHelpers.MulDiv

namespace Airbender.Compiler.NativeHelpers.ShiftBinop
open Airbender Airbender.Compiler Airbender.Trace NativeArithmetic

/-- Exact native timestamp matching bounds every physical helper value. -/
theorem bounded (initial : RV.State) (program : List RVMachineProgramEntry)
    (physical : GKRAddress → F)
    (accepted : Holds (NativeLookups.circuitFor (.pooled .shiftBinop)) physical)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .shiftBinop))
      (NativeLookups.selectorsFor (.pooled .shiftBinop)) physical (NativePublicSetup.rows initial program (.pooled .shiftBinop))) :
    ∀ field ∈ Airbender.Compiler.HelperNative.ShiftBinopCached.native.fields,
      (field.value (Airbender.Compiler.HelperNative.ShiftBinopCached.native.sourceValues physical)).val < 524288 := by
  intro field member
  let value := field.value (Airbender.Compiler.HelperNative.ShiftBinopCached.native.sourceValues physical)
  have present := NativeSourceTransport.ShiftBinop.source_member
    (NativeBindings.ShiftBinop.scalar_gates physical accepted) arguments 2 (MaterializedQuery.mk [value] 1)
    (by simpa [NativeSourceTransport.ShiftBinop.sourceRequests, value,
          Airbender.Compiler.HelperNative.ShiftBinopCached.native.sourceValues] using
        (List.mem_map.mpr ⟨field, member, rfl⟩ :
          MaterializedQuery.mk [field.value (Airbender.Compiler.HelperNative.ShiftBinopCached.native.sourceValues physical)] 1 ∈
            Airbender.Compiler.HelperNative.ShiftBinopCached.native.fields.map (fun item => MaterializedQuery.mk
              [item.value (Airbender.Compiler.HelperNative.ShiftBinopCached.native.sourceValues physical)] 1))) one_ne_zero
  obtain ⟨index, same⟩ := present
  exact NativePublicSetup.Proofs.timestamp_bound same

end Airbender.Compiler.NativeHelpers.ShiftBinop

namespace Airbender.Compiler.NativeHelpers.WordMemory
open Airbender Airbender.Compiler Airbender.Trace NativeArithmetic

/-- Exact native timestamp matching bounds every physical helper value. -/
theorem bounded (initial : RV.State) (program : List RVMachineProgramEntry)
    (physical : GKRAddress → F)
    (accepted : Holds (NativeLookups.circuitFor (.pooled .wordMemory)) physical)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .wordMemory))
      (NativeLookups.selectorsFor (.pooled .wordMemory)) physical (NativePublicSetup.rows initial program (.pooled .wordMemory))) :
    ∀ field ∈ Airbender.Compiler.HelperNative.WordMemoryCached.native.fields,
      (field.value (Airbender.Compiler.HelperNative.WordMemoryCached.native.sourceValues physical)).val < 524288 := by
  intro field member
  let value := field.value (Airbender.Compiler.HelperNative.WordMemoryCached.native.sourceValues physical)
  have present := NativeSourceTransport.WordMemory.source_member
    (NativeBindings.WordMemory.scalar_gates physical accepted) arguments 2 (MaterializedQuery.mk [value] 1)
    (by simpa [NativeSourceTransport.WordMemory.sourceRequests, value,
          Airbender.Compiler.HelperNative.WordMemoryCached.native.sourceValues] using
        (List.mem_map.mpr ⟨field, member, rfl⟩ :
          MaterializedQuery.mk [field.value (Airbender.Compiler.HelperNative.WordMemoryCached.native.sourceValues physical)] 1 ∈
            Airbender.Compiler.HelperNative.WordMemoryCached.native.fields.map (fun item => MaterializedQuery.mk
              [item.value (Airbender.Compiler.HelperNative.WordMemoryCached.native.sourceValues physical)] 1))) one_ne_zero
  obtain ⟨index, same⟩ := present
  exact NativePublicSetup.Proofs.timestamp_bound same

end Airbender.Compiler.NativeHelpers.WordMemory

namespace Airbender.Compiler.NativeHelpers.SubwordMemory
open Airbender Airbender.Compiler Airbender.Trace NativeArithmetic

/-- Exact native timestamp matching bounds every physical helper value. -/
theorem bounded (initial : RV.State) (program : List RVMachineProgramEntry)
    (physical : GKRAddress → F)
    (accepted : Holds (NativeLookups.circuitFor (.pooled .subwordMemory)) physical)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor (.pooled .subwordMemory))
      (NativeLookups.selectorsFor (.pooled .subwordMemory)) physical (NativePublicSetup.rows initial program (.pooled .subwordMemory))) :
    ∀ field ∈ Airbender.Compiler.HelperNative.SubwordMemoryCached.native.fields,
      (field.value (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.sourceValues physical)).val < 524288 := by
  intro field member
  let value := field.value (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.sourceValues physical)
  have present := NativeSourceTransport.SubwordMemory.source_member
    (NativeBindings.SubwordMemory.scalar_gates physical accepted) arguments 2 (MaterializedQuery.mk [value] 1)
    (by simpa [NativeSourceTransport.SubwordMemory.sourceRequests, value,
          Airbender.Compiler.HelperNative.SubwordMemoryCached.native.sourceValues] using
        (List.mem_map.mpr ⟨field, member, rfl⟩ :
          MaterializedQuery.mk [field.value (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.sourceValues physical)] 1 ∈
            Airbender.Compiler.HelperNative.SubwordMemoryCached.native.fields.map (fun item => MaterializedQuery.mk
              [item.value (Airbender.Compiler.HelperNative.SubwordMemoryCached.native.sourceValues physical)] 1))) one_ne_zero
  obtain ⟨index, same⟩ := present
  exact NativePublicSetup.Proofs.timestamp_bound same

end Airbender.Compiler.NativeHelpers.SubwordMemory

namespace Airbender.Compiler.NativeHelpers.Unified
open Airbender Airbender.Compiler Airbender.Trace NativeArithmetic

/-- Exact native timestamp matching bounds every physical helper value. -/
theorem bounded (initial : RV.State) (program : List RVMachineProgramEntry)
    (physical : GKRAddress → F)
    (accepted : Holds (NativeLookups.circuitFor .unified) physical)
    (arguments : NativeLookups.Arguments (NativeLookups.circuitFor .unified)
      (NativeLookups.selectorsFor .unified) physical (NativePublicSetup.rows initial program .unified)) :
    ∀ field ∈ Airbender.Compiler.HelperNative.UnifiedCached.native.fields,
      (field.value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues physical)).val < 524288 := by
  intro field member
  let value := field.value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues physical)
  have present := NativeSourceTransport.Unified.source_member
    (NativeBindings.Unified.scalar_gates physical accepted) arguments 2 (MaterializedQuery.mk [value] 1)
    (by simpa [NativeSourceTransport.Unified.sourceRequests, value,
          Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues] using
        (List.mem_map.mpr ⟨field, member, rfl⟩ :
          MaterializedQuery.mk [field.value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues physical)] 1 ∈
            Airbender.Compiler.HelperNative.UnifiedCached.native.fields.map (fun item => MaterializedQuery.mk
              [item.value (Airbender.Compiler.HelperNative.UnifiedCached.native.sourceValues physical)] 1))) one_ne_zero
  obtain ⟨index, same⟩ := present
  exact NativePublicSetup.Proofs.timestamp_bound same

end Airbender.Compiler.NativeHelpers.Unified
