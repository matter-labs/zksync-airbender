import Airbender.Proofs.GKRProtocol.CleanPlacementChecks

namespace Tests.CleanPlacementChecks
open Airbender Airbender.Compiler
open NumericPolynomialChecks
set_option warningAsError true

def entries : List GKRAddress := [.BaseLayerWitness 0, .BaseLayerMemory 1, .Cached 2 3]
def placements : List GKRAddress := [.Cached 2 3, .BaseLayerWitness 0]
def capture : CleanPlacementChecks.Capture := ⟨.leaf [0, 3, 127], [(127, 2), (0, 0)]⟩

theorem bank_binding : capture.bank.toList = entries.map AddressUniqueChecks.addressCode := by decide +kernel
theorem placement_binding : capture.references.map Prod.fst = placements.map AddressUniqueChecks.addressCode := by decide +kernel
theorem checked : CleanPlacementChecks.check capture = true := by decide +kernel

theorem original_roundtrips : placements.all (fun address => decide
    ((WireBank.ofList entries (by decide +kernel)).address
      ((WireBank.ofList entries (by decide +kernel)).placement address) = address)) = true :=
  CleanPlacementChecks.check_sound entries (by decide +kernel) (by decide +kernel)
    placements capture bank_binding placement_binding checked

def wrongIndex : CleanPlacementChecks.Capture := {capture with references := [(127, 1), (0, 0)]}
def wrongCode : CleanPlacementChecks.Capture := {capture with references := [(126, 2), (0, 0)]}
def outside : CleanPlacementChecks.Capture := {capture with references := [(127, 2), (0, 3)]}
def forgedSize : CleanPlacementChecks.Capture := {capture with bank := .branch 99 (.leaf [0]) (.leaf [3, 127])}

theorem wrong_index_rejected : CleanPlacementChecks.check wrongIndex = false := by decide +kernel
theorem wrong_code_rejected : CleanPlacementChecks.check wrongCode = false := by decide +kernel
theorem default_value_cannot_hide_outside_index : CleanPlacementChecks.check outside = false := by decide +kernel
theorem forged_size_rejected : CleanPlacementChecks.check forgedSize = false := by decide +kernel

end Tests.CleanPlacementChecks
