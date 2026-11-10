import Airbender.Import.SetupSourceBank

namespace Airbender.Setup.SourceBank

/-- Retain the source addresses and block selector of one physical column. -/
structure ColumnBinding where
  index : Nat
  keyIndex : Nat
  arrayIndex : Nat
  children : Nat → Nat
  blocks : Nat → Block
  entries : List Nat

def ColumnBinding.column (binding : ColumnBinding) : Column :=
  ⟨(binding.entries.map binding.blocks).toArray⟩

structure ValueArrayBinding where
  index : Nat
  children : Nat → Nat
  naturals : Nat → Nat
  entries : List Nat

def ValueArrayBinding.values (binding : ValueArrayBinding) : Array Nat :=
  (binding.entries.map binding.naturals).toArray

end Airbender.Setup.SourceBank
