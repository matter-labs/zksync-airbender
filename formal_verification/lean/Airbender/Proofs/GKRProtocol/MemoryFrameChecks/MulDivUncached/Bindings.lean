import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.MulDivUncached.PlacementBindings
import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.MulDivUncached.NativeAddressBindings
import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.MulDivUncached.InputAddressBindings
import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.MulDivUncached.FullAddressBindings
import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.MulDivUncached.FieldsBindings

namespace Airbender.Compiler.MemoryFrameChecks.MulDivUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_data_binding active_binding : data.activeMask = NumericQueryFrameChecks.coordinateMask (Airbender.Compiler.MemoryFrameNative.MulDivUncached.native.activeCoordinates.map Fin.val)

numeric_data_binding all_binding : data.allMask = NumericQueryFrameChecks.coordinateMask (Airbender.Compiler.MemoryFrameNative.MulDivUncached.native.allCoordinates.map Fin.val)

theorem placement_binding : data.placement.toList = List.ofFn (fun wire => (Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.inputBank.placement (Airbender.Compiler.MemoryNative.MulDivUncached.native.bank.address wire)).val) := by
  have same := congrArg (fun value : NumericMemoryFrameChecks.Capture => value.placement.toList)
    (NumericMemoryFrameChecks.ofTypedPrefix_eq Airbender.Compiler.MemoryFrameNative.MulDivUncached.native.ramFields Airbender.Compiler.MemoryFrameNative.MulDivUncached.native.initializationFields Airbender.Compiler.MemoryFrameNative.MulDivUncached.native.executeFields
  Airbender.Compiler.MemoryNative.MulDivUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.MulDivUncached.native.bank Airbender.Compiler.MemoryFrameNative.MulDivUncached.native.activeCoordinates Airbender.Compiler.MemoryFrameNative.MulDivUncached.native.allCoordinates
  Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.bank
      inputCoordinates inputRoundTrip Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.artifact.projection Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.inputCoordinates Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.bankRoundTrip)
  have bound : List.ofFn placementSource = List.ofFn (fun wire => (Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.inputBank.placement (Airbender.Compiler.MemoryNative.MulDivUncached.native.bank.address wire)).val) := by
    unfold placementSource
    simpa only [NumericMemoryFrameChecks.ofTypedPrefix, NumericMemoryFrameChecks.ofTyped, NumericPolynomialChecks.LookupTable.toList_ofList] using same
  exact placement_fast_binding.trans bound

theorem inputAddress_binding : data.inputAddress.toList = List.ofFn (fun wire => AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.inputBank.address (Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.inputBank.placement (Airbender.Compiler.MemoryNative.MulDivUncached.native.bank.address wire)))) := by
  have same := congrArg (fun value : NumericMemoryFrameChecks.Capture => value.inputAddress.toList)
    (NumericMemoryFrameChecks.ofTypedPrefix_eq Airbender.Compiler.MemoryFrameNative.MulDivUncached.native.ramFields Airbender.Compiler.MemoryFrameNative.MulDivUncached.native.initializationFields Airbender.Compiler.MemoryFrameNative.MulDivUncached.native.executeFields
  Airbender.Compiler.MemoryNative.MulDivUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.MulDivUncached.native.bank Airbender.Compiler.MemoryFrameNative.MulDivUncached.native.activeCoordinates Airbender.Compiler.MemoryFrameNative.MulDivUncached.native.allCoordinates
  Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.bank
      inputCoordinates inputRoundTrip Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.artifact.projection Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.inputCoordinates Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.bankRoundTrip)
  have bound : List.ofFn inputAddressSource = List.ofFn (fun wire => AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.inputBank.address (Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.inputBank.placement (Airbender.Compiler.MemoryNative.MulDivUncached.native.bank.address wire)))) := by
    unfold inputAddressSource
    simpa only [NumericMemoryFrameChecks.ofTypedPrefix, NumericMemoryFrameChecks.ofTyped, NumericPolynomialChecks.LookupTable.toList_ofList] using same
  exact inputAddress_fast_binding.trans bound

theorem fullAddress_binding : data.fullAddress.toList = List.ofFn (fun wire => AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.bank.address (Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.bank.placement (Airbender.Compiler.MemoryNative.MulDivUncached.native.bank.address wire)))) := by
  have same := congrArg (fun value : NumericMemoryFrameChecks.Capture => value.fullAddress.toList)
    (NumericMemoryFrameChecks.ofTypedPrefix_eq Airbender.Compiler.MemoryFrameNative.MulDivUncached.native.ramFields Airbender.Compiler.MemoryFrameNative.MulDivUncached.native.initializationFields Airbender.Compiler.MemoryFrameNative.MulDivUncached.native.executeFields
  Airbender.Compiler.MemoryNative.MulDivUncached.native.sourcePlacement Airbender.Compiler.MemoryNative.MulDivUncached.native.bank Airbender.Compiler.MemoryFrameNative.MulDivUncached.native.activeCoordinates Airbender.Compiler.MemoryFrameNative.MulDivUncached.native.allCoordinates
  Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.inputBank Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.bank
      inputCoordinates inputRoundTrip Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.artifact.projection Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.inputCoordinates Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.bankRoundTrip)
  have bound : List.ofFn fullAddressSource = List.ofFn (fun wire => AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.bank.address (Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.bank.placement (Airbender.Compiler.MemoryNative.MulDivUncached.native.bank.address wire)))) := by
    unfold fullAddressSource
    simpa only [NumericMemoryFrameChecks.ofTypedPrefix, NumericMemoryFrameChecks.ofTyped, NumericPolynomialChecks.LookupTable.toList_ofList] using same
  exact fullAddress_fast_binding.trans bound

theorem nativeAddress_binding : data.nativeAddress.toList = List.ofFn (fun wire => AddressUniqueChecks.addressCode (Airbender.Compiler.MemoryNative.MulDivUncached.native.bank.address wire)) := nativeAddress_fast_binding

end Airbender.Compiler.MemoryFrameChecks.MulDivUncached
