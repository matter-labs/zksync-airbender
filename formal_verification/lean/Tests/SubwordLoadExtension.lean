import Airbender.Proofs.SubwordMemory.LoadExtension
import Airbender.Review.Circuits.SubwordMemory.DataModel

namespace Tests.SubwordLoadExtension
open Airbender Arithmetic Verification SubwordMemory
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Signedness boundaries and all byte positions exercise independent values. -/
theorem signed_boundaries :
    SailRV32.Functions.extend_value false (0x7f : BitVec 8) = (0x7f : BitVec 32) ∧
    SailRV32.Functions.extend_value false (0x80 : BitVec 8) = (0xffffff80 : BitVec 32) ∧
    SailRV32.Functions.extend_value false (0x8000 : BitVec 16) = (0xffff8000 : BitVec 32) ∧
    SailRV32.Functions.extend_value true (0xffff : BitVec 16) = (0xffff : BitVec 32) := by
  decide +kernel

theorem native_byte_positions :
    SubwordLoad.limbs (0x80ff + 65536 * 0 + 262144 * 0) = (65535,65535) ∧
    SubwordLoad.limbs (0x80ff + 65536 * 1 + 262144 * 0) = (65408,65535) ∧
    SubwordLoad.limbs (0x80ff + 65536 * 2 + 262144 * 4) = (255,0) ∧
    SubwordLoad.limbs (0x80ff + 65536 * 3 + 262144 * 4) = (128,0) := by
  decide +kernel

/-- Odd halfword helper rows remain zero; native discarded-load trap handling
    is retained and no success of original instruction execution is asserted. -/
theorem odd_halfword_rows :
    SubwordLoad.limbs (65535 + 65536 * 1 + 262144 * 1) = (0,0) ∧
    SubwordLoad.limbs (65535 + 65536 * 3 + 262144 * 5) = (0,0) := by
  decide +kernel

end Tests.SubwordLoadExtension
