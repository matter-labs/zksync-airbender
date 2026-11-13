module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.BaseAffine
public import Proven.GKRProtocol.NumericPolynomialChecks
public import Proven.GKRProtocol.CleanPlacementChecks

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.NumericFunctionalBaseChecks

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

structure TypedPort where
  address : GKRAddress
  returned : GKRAddress
  base : Bool

def TypedPort.check (port : TypedPort) : Bool :=
  addressEqual port.returned port.address && port.base

structure Typed (n p : Nat) where
  ports : List TypedPort
  left : Polynomial n (ZMod p)
  right : Polynomial n (ZMod p)

def Typed.check [NeZero p] (source : Typed n p) : Bool :=
  source.ports.all TypedPort.check && Airbender.Compiler.equal source.left source.right

structure Data where
  ports : List (Nat × Nat × Nat)
  left : NumericPolynomialChecks.Data
  right : NumericPolynomialChecks.Data

def encodePort (port : TypedPort) : Nat × Nat × Nat :=
  (AddressUniqueChecks.addressCode port.returned,
   AddressUniqueChecks.addressCode port.address, if port.base then 1 else 0)

def encode (source : Typed n p) : Data :=
  ⟨source.ports.map encodePort, NumericPolynomialChecks.encode source.left,
    NumericPolynomialChecks.encode source.right⟩

def portCheck (port : Nat × Nat × Nat) : Bool := port.1 == port.2.1 && port.2.2 == 1

def entryCheck (p : Nat) (data : Data) : Bool :=
  data.ports.all portCheck && NumericPolynomialChecks.equal p data.left data.right

def check (p : Nat) (data : List Data) : Bool := data.all (entryCheck p)

theorem address_code_equal (left right : GKRAddress) :
    (AddressUniqueChecks.addressCode left == AddressUniqueChecks.addressCode right) = addressEqual left right := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, addressEqual_iff, CleanPlacementChecks.addressCode_injective.eq_iff]

theorem port_encode (port : TypedPort) : portCheck (encodePort port) = port.check := by
  simp only [portCheck, encodePort, TypedPort.check, address_code_equal]
  cases port.base <;> rfl

theorem entry_encode [NeZero p] (source : Typed n p) : entryCheck p (encode source) = source.check := by
  simp only [entryCheck, encode, Typed.check, List.all_map, Function.comp_def, port_encode,
    NumericPolynomialChecks.equal_encode]

theorem check_sound [NeZero p] (sources : List (Typed n p)) (data : List Data)
    (binding : data = sources.map encode) (checked : check p data = true) :
    sources.all Typed.check = true := by
  rw [binding] at checked
  simpa only [check, List.all_map, Function.comp_def, entry_encode] using checked

def ofBase (recipe : NativeBaseRecipe) (output : GKRAddress) (bank : WireBank n)
    (isBase : GKRAddress → Bool) (residual : Polynomial n Source.BaseField) : Typed n babyBearModulus :=
  ⟨(output :: recipe.inputs).map (fun address => ⟨address, bank.address (bank.placement address), isBase address⟩),
    recipe.relation bank output, residual⟩

theorem ofBase_check (recipe : NativeBaseRecipe) (output : GKRAddress) (bank : WireBank n)
    (isBase : GKRAddress → Bool) (residual : Polynomial n Source.BaseField) :
    (ofBase recipe output bank isBase residual).check =
      (recipe.portsCheck bank isBase output && Airbender.Compiler.equal (recipe.relation bank output) residual) := by
  simp only [Typed.check, ofBase, NativeBaseRecipe.portsCheck, List.all_map, Function.comp_def, TypedPort.check]

end Airbender.Compiler.NumericFunctionalBaseChecks
