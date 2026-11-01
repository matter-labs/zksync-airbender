import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.BlakeGUncached.PlacementBindings
import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.BlakeGUncached.NativeAddressBindings
import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.BlakeGUncached.InputAddressBindings
import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.BlakeGUncached.FullAddressBindings
import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.BlakeGUncached.FieldsBindings

namespace Airbender.Compiler.MemoryFrameChecks.BlakeGUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_data_binding active_binding : data.activeMask = NumericQueryFrameChecks.coordinateMask (Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native.activeCoordinates.map Fin.val)

numeric_data_binding all_binding : data.allMask = NumericQueryFrameChecks.coordinateMask (Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native.allCoordinates.map Fin.val)

theorem placement_binding : data.placement.toList = List.ofFn (fun wire => (Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.inputBank.placement (Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank.address wire)).val) := by
  have same := congrArg (fun value : NumericMemoryFrameChecks.Capture => value.placement.toList)
    (NumericMemoryFrameChecks.ofTypedPrefix_eq Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native.ramFields Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native.initializationFields Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native.executeFields
  Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native.activeCoordinates Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native.allCoordinates
  Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.bank
      inputCoordinates inputRoundTrip Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.artifact.projection Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.inputCoordinates Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.bankRoundTrip)
  have bound : List.ofFn placementSource = List.ofFn (fun wire => (Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.inputBank.placement (Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank.address wire)).val) := by
    unfold placementSource
    simpa only [NumericMemoryFrameChecks.ofTypedPrefix, NumericMemoryFrameChecks.ofTyped, NumericPolynomialChecks.LookupTable.toList_ofList] using same
  exact placement_fast_binding.trans bound

theorem inputAddress_binding : data.inputAddress.toList = List.ofFn (fun wire => AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.inputBank.address (Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.inputBank.placement (Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank.address wire)))) := by
  have same := congrArg (fun value : NumericMemoryFrameChecks.Capture => value.inputAddress.toList)
    (NumericMemoryFrameChecks.ofTypedPrefix_eq Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native.ramFields Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native.initializationFields Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native.executeFields
  Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native.activeCoordinates Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native.allCoordinates
  Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.bank
      inputCoordinates inputRoundTrip Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.artifact.projection Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.inputCoordinates Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.bankRoundTrip)
  have bound : List.ofFn inputAddressSource = List.ofFn (fun wire => AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.inputBank.address (Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.inputBank.placement (Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank.address wire)))) := by
    unfold inputAddressSource
    simpa only [NumericMemoryFrameChecks.ofTypedPrefix, NumericMemoryFrameChecks.ofTyped, NumericPolynomialChecks.LookupTable.toList_ofList] using same
  exact inputAddress_fast_binding.trans bound

theorem fullAddress_binding : data.fullAddress.toList = List.ofFn (fun wire => AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.bank.placement (Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank.address wire)))) := by
  have same := congrArg (fun value : NumericMemoryFrameChecks.Capture => value.fullAddress.toList)
    (NumericMemoryFrameChecks.ofTypedPrefix_eq Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native.ramFields Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native.initializationFields Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native.executeFields
  Airbender.Compiler.MemoryNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native.activeCoordinates Airbender.Compiler.MemoryFrameNative.BlakeGUncached.native.allCoordinates
  Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.bank
      inputCoordinates inputRoundTrip Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.artifact.projection Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.inputCoordinates Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.bankRoundTrip)
  have bound : List.ofFn fullAddressSource = List.ofFn (fun wire => AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.bank.address (Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.bank.placement (Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank.address wire)))) := by
    unfold fullAddressSource
    simpa only [NumericMemoryFrameChecks.ofTypedPrefix, NumericMemoryFrameChecks.ofTyped, NumericPolynomialChecks.LookupTable.toList_ofList] using same
  exact fullAddress_fast_binding.trans bound

theorem nativeAddress_binding : data.nativeAddress.toList = List.ofFn (fun wire => AddressUniqueChecks.addressCode (Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank.address wire)) := nativeAddress_fast_binding

end Airbender.Compiler.MemoryFrameChecks.BlakeGUncached
