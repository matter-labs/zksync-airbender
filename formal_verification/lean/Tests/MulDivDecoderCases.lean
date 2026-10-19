import Tests.MulDivPublicProgram
import Airbender.Proofs.Sail.Sequential

namespace Tests.MulDivInitializedFixture
open Airbender MulDiv Trace

-- Reuse the pinned original decoder/read-continuation certificate structure.
-- Each original opcode is checked independently under the shared watchdog.
set_option maxRecDepth 32768 in
private theorem mul_decode (discarded : Bool) (state : Reference.RiscV.Sail.State)
    (isa : Reference.Sail.run (SailRV32.readReg .misa) state =
      .ok (0x40001000 : BitVec 32) state) :
    Reference.Sail.run (SailRV32.Functions.encdec_backwards (word .mul discarded)) state =
      .ok (instruction .mul discarded) state := by
  cases discarded
  all_goals
    repeat' first
      | (with_unfolding_all rfl)
      | (with_unfolding_all conv_lhs => arg 1; whnf
         rw [@Reference.Sail.run_read_cont (inferInstance : _root_.Sail.ArchSem.Arch)
           _ _ SailRV32.Register.misa _ _ _ isa])
set_option maxRecDepth 32768 in
private theorem mulhu_decode (discarded : Bool) (state : Reference.RiscV.Sail.State)
    (isa : Reference.Sail.run (SailRV32.readReg .misa) state =
      .ok (0x40001000 : BitVec 32) state) :
    Reference.Sail.run (SailRV32.Functions.encdec_backwards (word .mulhu discarded)) state =
      .ok (instruction .mulhu discarded) state := by
  cases discarded
  all_goals
    repeat' first
      | (with_unfolding_all rfl)
      | (with_unfolding_all conv_lhs => arg 1; whnf
         rw [@Reference.Sail.run_read_cont (inferInstance : _root_.Sail.ArchSem.Arch)
           _ _ SailRV32.Register.misa _ _ _ isa])
set_option maxRecDepth 32768 in
private theorem divu_decode (discarded : Bool) (state : Reference.RiscV.Sail.State)
    (isa : Reference.Sail.run (SailRV32.readReg .misa) state =
      .ok (0x40001000 : BitVec 32) state) :
    Reference.Sail.run (SailRV32.Functions.encdec_backwards (word .divu discarded)) state =
      .ok (instruction .divu discarded) state := by
  cases discarded
  all_goals
    repeat' first
      | (with_unfolding_all rfl)
      | (with_unfolding_all conv_lhs => arg 1; whnf
         rw [@Reference.Sail.run_read_cont (inferInstance : _root_.Sail.ArchSem.Arch)
           _ _ SailRV32.Register.misa _ _ _ isa])
set_option maxRecDepth 32768 in
private theorem remu_decode (discarded : Bool) (state : Reference.RiscV.Sail.State)
    (isa : Reference.Sail.run (SailRV32.readReg .misa) state =
      .ok (0x40001000 : BitVec 32) state) :
    Reference.Sail.run (SailRV32.Functions.encdec_backwards (word .remu discarded)) state =
      .ok (instruction .remu discarded) state := by
  cases discarded
  all_goals
    repeat' first
      | (with_unfolding_all rfl)
      | (with_unfolding_all conv_lhs => arg 1; whnf
         rw [@Reference.Sail.run_read_cont (inferInstance : _root_.Sail.ArchSem.Arch)
           _ _ SailRV32.Register.misa _ _ _ isa])

theorem original_decode (op : Operation) (discarded : Bool) (state : Reference.RiscV.Sail.State)
    (isa : Reference.Sail.run (SailRV32.readReg .misa) state =
      .ok (0x40001000 : BitVec 32) state) :
    Reference.Sail.run (SailRV32.Functions.encdec_backwards (word op discarded)) state =
      .ok (instruction op discarded) state := by
  cases op
  · exact mul_decode discarded state isa
  · exact mulhu_decode discarded state isa
  · exact divu_decode discarded state isa
  · exact remu_decode discarded state isa

def decodedSlot (state : Reference.RiscV.Sail.State) (pc bits : BitVec 32) :
    Option (Option MulDiv.ProgramEntry) :=
  match Reference.Sail.run (SailRV32.Functions.encdec_backwards bits) state with
  | .ok instruction _ => some ((MulDiv.decoderFields instruction).map fun data => ⟨pc,bits,instruction,data⟩)
  | .error _ _ => none

theorem decoded_slot (op : Operation) (discarded : Bool) (state : Reference.RiscV.Sail.State)
    (isa : Reference.Sail.run (SailRV32.readReg .misa) state =
      .ok (0x40001000 : BitVec 32) state) :
    decodedSlot state 0 (word op discarded) = some (some (entry op discarded)) := by
  rw [decodedSlot,original_decode op discarded state isa]
  cases op <;> cases discarded <;> rfl

set_option maxRecDepth 32768 in
theorem decoded_hole (state : Reference.RiscV.Sail.State) :
    decodedSlot state 4 0xc0001073 = some none := by
  with_unfolding_all rfl

set_option maxRecDepth 32768 in
private theorem mul_disabled (discarded : Bool) (state : Reference.RiscV.Sail.State)
    (isa : Reference.Sail.run (SailRV32.readReg .misa) state =
      .ok (0x40000000 : BitVec 32) state) :
    Reference.Sail.run (SailRV32.Functions.encdec_backwards (word .mul discarded)) state =
      .error (_root_.Sail.Error.Assertion "Pattern match failure at unknown location") state := by
  cases discarded
  all_goals
    repeat' first
      | (with_unfolding_all rfl)
      | (with_unfolding_all conv_lhs => arg 1; whnf
         rw [@Reference.Sail.run_read_cont (inferInstance : _root_.Sail.ArchSem.Arch)
           _ _ SailRV32.Register.misa _ _ _ isa])
set_option maxRecDepth 32768 in
private theorem mulhu_disabled (discarded : Bool) (state : Reference.RiscV.Sail.State)
    (isa : Reference.Sail.run (SailRV32.readReg .misa) state =
      .ok (0x40000000 : BitVec 32) state) :
    Reference.Sail.run (SailRV32.Functions.encdec_backwards (word .mulhu discarded)) state =
      .error (_root_.Sail.Error.Assertion "Pattern match failure at unknown location") state := by
  cases discarded
  all_goals
    repeat' first
      | (with_unfolding_all rfl)
      | (with_unfolding_all conv_lhs => arg 1; whnf
         rw [@Reference.Sail.run_read_cont (inferInstance : _root_.Sail.ArchSem.Arch)
           _ _ SailRV32.Register.misa _ _ _ isa])
set_option maxRecDepth 32768 in
private theorem divu_disabled (discarded : Bool) (state : Reference.RiscV.Sail.State)
    (isa : Reference.Sail.run (SailRV32.readReg .misa) state =
      .ok (0x40000000 : BitVec 32) state) :
    Reference.Sail.run (SailRV32.Functions.encdec_backwards (word .divu discarded)) state =
      .error (_root_.Sail.Error.Assertion "Pattern match failure at unknown location") state := by
  cases discarded
  all_goals
    repeat' first
      | (with_unfolding_all rfl)
      | (with_unfolding_all conv_lhs => arg 1; whnf
         rw [@Reference.Sail.run_read_cont (inferInstance : _root_.Sail.ArchSem.Arch)
           _ _ SailRV32.Register.misa _ _ _ isa])
set_option maxRecDepth 32768 in
private theorem remu_disabled (discarded : Bool) (state : Reference.RiscV.Sail.State)
    (isa : Reference.Sail.run (SailRV32.readReg .misa) state =
      .ok (0x40000000 : BitVec 32) state) :
    Reference.Sail.run (SailRV32.Functions.encdec_backwards (word .remu discarded)) state =
      .error (_root_.Sail.Error.Assertion "Pattern match failure at unknown location") state := by
  cases discarded
  all_goals
    repeat' first
      | (with_unfolding_all rfl)
      | (with_unfolding_all conv_lhs => arg 1; whnf
         rw [@Reference.Sail.run_read_cont (inferInstance : _root_.Sail.ArchSem.Arch)
           _ _ SailRV32.Register.misa _ _ _ isa])

/-- Original configuration reads are observable: disabled M is a decoder error,
    even for x0 destinations. It does not construct a supported slot or a hole. -/
theorem disabled_extension_rejected (op : Operation) (discarded : Bool)
    (state : Reference.RiscV.Sail.State)
    (isa : Reference.Sail.run (SailRV32.readReg .misa) state =
      .ok (0x40000000 : BitVec 32) state) :
    decodedSlot state 0 (word op discarded) = none := by
  unfold decodedSlot
  cases op
  · rw [mul_disabled discarded state isa]
  · rw [mulhu_disabled discarded state isa]
  · rw [divu_disabled discarded state isa]
  · rw [remu_disabled discarded state isa]

end Tests.MulDivInitializedFixture
