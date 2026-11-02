import Airbender.Proofs.GKRProtocol.NumericFunctionalBaseChecks

namespace Airbender.Compiler.NumericSourceFreshnessChecks
set_option warningAsError true

def ofAddress (address : GKRAddress) : NumericFunctionalBaseChecks.Typed 0 1 :=
  ⟨[⟨address, address, true⟩], [], []⟩

def encodeAddresses (addresses : List GKRAddress) : List NumericFunctionalBaseChecks.Data :=
  addresses.map (fun address => NumericFunctionalBaseChecks.encode (ofAddress address))

def codes (data : List NumericFunctionalBaseChecks.Data) : List Nat :=
  data.map (fun row => (row.ports.headD (0, 0, 0)).1)

theorem codes_encode (addresses : List GKRAddress) :
    codes (encodeAddresses addresses) = addresses.map AddressUniqueChecks.addressCode := by
  simp [codes, encodeAddresses, ofAddress, NumericFunctionalBaseChecks.encode,
    NumericFunctionalBaseChecks.encodePort]

def check (sources targets : List NumericFunctionalBaseChecks.Data) : Bool :=
  (codes targets).all (fun target => (codes sources).all (fun source => !(source == target)))

theorem check_sound (sources targets : List GKRAddress)
    (sourceData targetData : List NumericFunctionalBaseChecks.Data)
    (sourceBinding : sourceData = encodeAddresses sources)
    (targetBinding : targetData = encodeAddresses targets)
    (checked : check sourceData targetData = true) :
    targets.all (fun target => sources.all (fun source => !addressEqual source target)) = true := by
  rw [sourceBinding, targetBinding] at checked
  simpa only [check, codes_encode, List.all_map, Function.comp_def,
    NumericFunctionalBaseChecks.address_code_equal] using checked

end Airbender.Compiler.NumericSourceFreshnessChecks
