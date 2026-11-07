import Airbender.Review.Circuits.ReducedMachine.WordMemoryTheorems

namespace Tests.NativeReducedWordMemoryRouting
open Airbender ReducedMachine Native Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

theorem masks : wordMemoryMask false = 1025 ∧ wordMemoryMask true = 16386 := ⟨rfl,rfl⟩

theorem bit_positions : (List.range 18).map (NativeWordMemorySelectorProofs.bit false) =
    [1,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0] ∧
    (List.range 18).map (NativeWordMemorySelectorProofs.bit true) =
    [0,1,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0] := ⟨rfl,rfl⟩

/-- LW port1 is a real memory event, including its retained shadow read. -/
theorem load_register_space_rejected {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (mask : w 12 = (1025 : ZMod mersenne31Modulus)) (bad : w 88 ≠ 0) : False :=
  bad (word_memory_routing holds false mask).secondSpace

/-- SW port2 is a real memory write, not a discarded architectural x0 write. -/
theorem store_register_space_rejected {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (mask : w 12 = (16386 : ZMod mersenne31Modulus)) (bad : w 89 ≠ 0) : False :=
  bad (word_memory_routing holds true mask).thirdSpace

/-- LW selects native immediate fields while its second actual event remains memory. -/
theorem load_operand {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (mask : w 12 = (1025 : ZMod mersenne31Modulus)) : #v[w 47,w 48] = #v[w 9,w 10] :=
  (word_memory_routing holds false mask).operand

/-- SW selects actual second-port input; destination-address arithmetic stays open. -/
theorem store_operand {fixed : Table (ZMod mersenne31Modulus) (fields 4)}
    {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints fixed))
    (mask : w 12 = (16386 : ZMod mersenne31Modulus)) : #v[w 47,w 48] = #v[w 37,w 38] :=
  (word_memory_routing holds true mask).operand

end Tests.NativeReducedWordMemoryRouting
