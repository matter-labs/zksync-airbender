import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.JumpBranchUncached.PlacementBindings
import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.JumpBranchUncached.NativeAddressBindings
import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.JumpBranchUncached.InputAddressBindings
import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.JumpBranchUncached.FullAddressBindings
import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.JumpBranchUncached.FieldsBindings

namespace Airbender.Compiler.MemoryFrameChecks.JumpBranchUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_data_binding active_binding : data.activeMask = NumericQueryFrameChecks.coordinateMask (Airbender.Compiler.MemoryFrameNative.JumpBranchUncached.native.activeCoordinates.map Fin.val)

numeric_data_binding all_binding : data.allMask = NumericQueryFrameChecks.coordinateMask (Airbender.Compiler.MemoryFrameNative.JumpBranchUncached.native.allCoordinates.map Fin.val)

theorem placement_binding : data.placement.toList = List.ofFn (fun wire => (Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputBank.placement (Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank.address wire)).val) := by
  have same := congrArg (fun value : NumericMemoryFrameChecks.Capture => value.placement.toList)
    (NumericMemoryFrameChecks.ofTypedPrefix_eq Airbender.Compiler.MemoryFrameNative.JumpBranchUncached.native.ramFields Airbender.Compiler.MemoryFrameNative.JumpBranchUncached.native.initializationFields Airbender.Compiler.MemoryFrameNative.JumpBranchUncached.native.executeFields
  Airbender.Compiler.MemoryNative.JumpBranchUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank Airbender.Compiler.MemoryFrameNative.JumpBranchUncached.native.activeCoordinates Airbender.Compiler.MemoryFrameNative.JumpBranchUncached.native.allCoordinates
  Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.bank
      inputCoordinates inputRoundTrip Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.artifact.projection Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputCoordinates Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.bankRoundTrip)
  have bound : List.ofFn placementSource = List.ofFn (fun wire => (Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputBank.placement (Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank.address wire)).val) := by
    unfold placementSource
    simpa only [NumericMemoryFrameChecks.ofTypedPrefix, NumericMemoryFrameChecks.ofTyped, NumericPolynomialChecks.LookupTable.toList_ofList] using same
  exact placement_fast_binding.trans bound

theorem inputAddress_binding : data.inputAddress.toList = List.ofFn (fun wire => AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputBank.address (Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputBank.placement (Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank.address wire)))) := by
  have same := congrArg (fun value : NumericMemoryFrameChecks.Capture => value.inputAddress.toList)
    (NumericMemoryFrameChecks.ofTypedPrefix_eq Airbender.Compiler.MemoryFrameNative.JumpBranchUncached.native.ramFields Airbender.Compiler.MemoryFrameNative.JumpBranchUncached.native.initializationFields Airbender.Compiler.MemoryFrameNative.JumpBranchUncached.native.executeFields
  Airbender.Compiler.MemoryNative.JumpBranchUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank Airbender.Compiler.MemoryFrameNative.JumpBranchUncached.native.activeCoordinates Airbender.Compiler.MemoryFrameNative.JumpBranchUncached.native.allCoordinates
  Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.bank
      inputCoordinates inputRoundTrip Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.artifact.projection Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputCoordinates Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.bankRoundTrip)
  have bound : List.ofFn inputAddressSource = List.ofFn (fun wire => AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputBank.address (Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputBank.placement (Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank.address wire)))) := by
    unfold inputAddressSource
    simpa only [NumericMemoryFrameChecks.ofTypedPrefix, NumericMemoryFrameChecks.ofTyped, NumericPolynomialChecks.LookupTable.toList_ofList] using same
  exact inputAddress_fast_binding.trans bound

theorem fullAddress_binding : data.fullAddress.toList = List.ofFn (fun wire => AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.bank.placement (Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank.address wire)))) := by
  have same := congrArg (fun value : NumericMemoryFrameChecks.Capture => value.fullAddress.toList)
    (NumericMemoryFrameChecks.ofTypedPrefix_eq Airbender.Compiler.MemoryFrameNative.JumpBranchUncached.native.ramFields Airbender.Compiler.MemoryFrameNative.JumpBranchUncached.native.initializationFields Airbender.Compiler.MemoryFrameNative.JumpBranchUncached.native.executeFields
  Airbender.Compiler.MemoryNative.JumpBranchUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank Airbender.Compiler.MemoryFrameNative.JumpBranchUncached.native.activeCoordinates Airbender.Compiler.MemoryFrameNative.JumpBranchUncached.native.allCoordinates
  Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.bank
      inputCoordinates inputRoundTrip Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.artifact.projection Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.inputCoordinates Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.bankRoundTrip)
  have bound : List.ofFn fullAddressSource = List.ofFn (fun wire => AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.bank.address (Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.bank.placement (Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank.address wire)))) := by
    unfold fullAddressSource
    simpa only [NumericMemoryFrameChecks.ofTypedPrefix, NumericMemoryFrameChecks.ofTyped, NumericPolynomialChecks.LookupTable.toList_ofList] using same
  exact fullAddress_fast_binding.trans bound

theorem nativeAddress_binding : data.nativeAddress.toList = List.ofFn (fun wire => AddressUniqueChecks.addressCode (Airbender.Compiler.MemoryNative.JumpBranchUncached.native.bank.address wire)) := nativeAddress_fast_binding

end Airbender.Compiler.MemoryFrameChecks.JumpBranchUncached
