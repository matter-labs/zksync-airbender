import Airbender.Review.Circuits.ReducedMachine.Tables.Native

namespace Airbender.ReducedMachine.NativeFixed
/-- Reference meaning of the explicit native fixture, not a universal CSR allow-list. -/
def csrSupported (key : Nat) : Nat := if key = 1984 ∨ key = 1988 ∨ key = 1989 then 1 else 0
def csrDelegated (key : Nat) : Nat := if key = 1988 ∨ key = 1989 then 1 else 0
def csrRow (key : Nat) : Vector Nat 4 := #v[key,csrSupported key,csrDelegated key,25]
end Airbender.ReducedMachine.NativeFixed
