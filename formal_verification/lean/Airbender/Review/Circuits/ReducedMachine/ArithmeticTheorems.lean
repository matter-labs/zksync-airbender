import Airbender.Proofs.ReducedMachine.NativeArithmeticResult

namespace Airbender.ReducedMachine.Native
open Verification

/-- Actual arithmetic routing/tags/default-PC selection under the explicit native
    decoded mask. Original public decoding and initialized execution are separate. -/
theorem arithmetic_routing {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : ArithmeticMode) (mask : w 12 = (mode.mask : ZMod mersenne31Modulus)) :
    source2 w = (if mode.useRegister then #v[w 37,w 38] else #v[w 9,w 10]) ∧
      w 39 = w 6 ∧ w 40 = 0 ∧ w 88 = 1 ∧
      lookupSelectors w = #v[0,0,0,0] ∧ finalPC w = defaultPC w :=
  ⟨NativeArithmeticFieldProofs.source holds mode mask,
    (NativeArithmeticFieldProofs.source_port holds mode mask).1,
    (NativeArithmeticFieldProofs.source_port holds mode mask).2.1,
    (NativeArithmeticFieldProofs.source_port holds mode mask).2.2,
    NativeArithmeticFieldProofs.tags holds mode mask,NativeArithmeticFieldProofs.pc holds mode mask⟩

/-- Actual candidate and original native destination mask/address. The original
    public rd/x0 decoder connection is not supplied by a numerical candidate. -/
theorem arithmetic_masked_write {setup : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints setup))
    (mode : ArithmeticMode) (mask : w 12 = (mode.mask : ZMod mersenne31Modulus)) :
    arithmeticCandidate w = (if mode = .lui then #v[w 9,w 10] else #v[w 61,w 62]) ∧
      rdPort.address.code w = Nat.pair 0 (Nat.pair (rdIndex w).val 0) ∧
      rdWrite w = (arithmeticCandidate w).map (fun value => (1 - rdZeroFlag w) * value) :=
  ⟨NativeArithmeticFieldProofs.candidate holds mode mask,NativeArithmeticFieldProofs.write holds mode mask⟩

end Airbender.ReducedMachine.Native
