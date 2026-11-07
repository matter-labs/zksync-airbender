import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.SubwordMemoryCached.PlacementBindings
import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.SubwordMemoryCached.NativeAddressBindings
import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.SubwordMemoryCached.InputAddressBindings
import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.SubwordMemoryCached.FullAddressBindings
import Airbender.Proofs.GKRProtocol.MemoryFrameChecks.SubwordMemoryCached.FieldsBindings

namespace Airbender.Compiler.MemoryFrameChecks.SubwordMemoryCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

numeric_data_binding active_binding : data.activeMask = NumericQueryFrameChecks.coordinateMask (Airbender.Compiler.MemoryFrameNative.SubwordMemoryCached.native.activeCoordinates.map Fin.val)

numeric_data_binding all_binding : data.allMask = NumericQueryFrameChecks.coordinateMask (Airbender.Compiler.MemoryFrameNative.SubwordMemoryCached.native.allCoordinates.map Fin.val)

theorem placement_binding : data.placement.toList = List.ofFn (fun wire => (Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.inputBank.placement (Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank.address wire)).val) := by
  have same := congrArg (fun value : NumericMemoryFrameChecks.Capture => value.placement.toList)
    (NumericMemoryFrameChecks.ofTypedPrefix_eq Airbender.Compiler.MemoryFrameNative.SubwordMemoryCached.native.ramFields Airbender.Compiler.MemoryFrameNative.SubwordMemoryCached.native.initializationFields Airbender.Compiler.MemoryFrameNative.SubwordMemoryCached.native.executeFields
  Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.sourcePlacement Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank Airbender.Compiler.MemoryFrameNative.SubwordMemoryCached.native.activeCoordinates Airbender.Compiler.MemoryFrameNative.SubwordMemoryCached.native.allCoordinates
  Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.inputBank Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank
      inputCoordinates inputRoundTrip Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.artifact.projection Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.inputCoordinates Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bankRoundTrip)
  have bound : List.ofFn placementSource = List.ofFn (fun wire => (Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.inputBank.placement (Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank.address wire)).val) := by
    unfold placementSource
    simpa only [NumericMemoryFrameChecks.ofTypedPrefix, NumericMemoryFrameChecks.ofTyped, NumericPolynomialChecks.LookupTable.toList_ofList] using same
  exact placement_fast_binding.trans bound

theorem inputAddress_binding : data.inputAddress.toList = List.ofFn (fun wire => AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.inputBank.address (Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.inputBank.placement (Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank.address wire)))) := by
  have same := congrArg (fun value : NumericMemoryFrameChecks.Capture => value.inputAddress.toList)
    (NumericMemoryFrameChecks.ofTypedPrefix_eq Airbender.Compiler.MemoryFrameNative.SubwordMemoryCached.native.ramFields Airbender.Compiler.MemoryFrameNative.SubwordMemoryCached.native.initializationFields Airbender.Compiler.MemoryFrameNative.SubwordMemoryCached.native.executeFields
  Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.sourcePlacement Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank Airbender.Compiler.MemoryFrameNative.SubwordMemoryCached.native.activeCoordinates Airbender.Compiler.MemoryFrameNative.SubwordMemoryCached.native.allCoordinates
  Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.inputBank Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank
      inputCoordinates inputRoundTrip Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.artifact.projection Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.inputCoordinates Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bankRoundTrip)
  have bound : List.ofFn inputAddressSource = List.ofFn (fun wire => AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.inputBank.address (Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.inputBank.placement (Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank.address wire)))) := by
    unfold inputAddressSource
    simpa only [NumericMemoryFrameChecks.ofTypedPrefix, NumericMemoryFrameChecks.ofTyped, NumericPolynomialChecks.LookupTable.toList_ofList] using same
  exact inputAddress_fast_binding.trans bound

theorem fullAddress_binding : data.fullAddress.toList = List.ofFn (fun wire => AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.placement (Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank.address wire)))) := by
  have same := congrArg (fun value : NumericMemoryFrameChecks.Capture => value.fullAddress.toList)
    (NumericMemoryFrameChecks.ofTypedPrefix_eq Airbender.Compiler.MemoryFrameNative.SubwordMemoryCached.native.ramFields Airbender.Compiler.MemoryFrameNative.SubwordMemoryCached.native.initializationFields Airbender.Compiler.MemoryFrameNative.SubwordMemoryCached.native.executeFields
  Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.sourcePlacement Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank Airbender.Compiler.MemoryFrameNative.SubwordMemoryCached.native.activeCoordinates Airbender.Compiler.MemoryFrameNative.SubwordMemoryCached.native.allCoordinates
  Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.inputBank Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank
      inputCoordinates inputRoundTrip Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.artifact.projection Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.inputCoordinates Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bankRoundTrip)
  have bound : List.ofFn fullAddressSource = List.ofFn (fun wire => AddressUniqueChecks.addressCode (Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.address (Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank.placement (Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank.address wire)))) := by
    unfold fullAddressSource
    simpa only [NumericMemoryFrameChecks.ofTypedPrefix, NumericMemoryFrameChecks.ofTyped, NumericPolynomialChecks.LookupTable.toList_ofList] using same
  exact fullAddress_fast_binding.trans bound

theorem nativeAddress_binding : data.nativeAddress.toList = List.ofFn (fun wire => AddressUniqueChecks.addressCode (Airbender.Compiler.MemoryNative.SubwordMemoryCached.native.bank.address wire)) := nativeAddress_fast_binding

end Airbender.Compiler.MemoryFrameChecks.SubwordMemoryCached
