import Slop.UnifiedReduced.Claims
import Slop.Sail.WordMemoryState

namespace Tests.UnifiedDecoder
open Airbender Arithmetic Trace Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

private def before (bits : BitVec 32) : State := wordWriteState default 0 bits
private def samples : List (BitVec 32 × SailRV32.instruction × DecoderData UnifiedFamily) := [
  (0x002081b3, .RTYPE (.Regidx 2, .Regidx 1, .Regidx 3, .ADD), ⟨.machine, 1, 2, 3, ⟨0, 0⟩, 1, 0⟩),
  (0x402081b3, .RTYPE (.Regidx 2, .Regidx 1, .Regidx 3, .SUB), ⟨.machine, 1, 2, 3, ⟨0, 0⟩, 2, 0⟩),
  (0xfff08193, .ITYPE (0xfff, .Regidx 1, .Regidx 3, .ADDI), ⟨.machine, 1, 0, 3, ⟨65535, 65535⟩, 1, 0⟩),
  (0x123451b7, .UTYPE (0x12345, .Regidx 3, .LUI), ⟨.machine, 0, 0, 3, ⟨20480, 4660⟩, 1, 0⟩),
  (0x12345197, .UTYPE (0x12345, .Regidx 3, .AUIPC), ⟨.machine, 0, 0, 3, ⟨20480, 4660⟩, 4, 0⟩),
  (0x0000a183, .LOAD (0, .Regidx 1, .Regidx 3, false, 4), ⟨.machine, 1, 0, 3, ⟨0, 0⟩, 131072, 0⟩),
  (0x0020a023, .STORE (0, .Regidx 2, .Regidx 1, 4), ⟨.machine, 1, 2, 0, ⟨0, 0⟩, 262144, 0⟩),
  (0x0020a1b3, .RTYPE (.Regidx 2, .Regidx 1, .Regidx 3, .SLT), ⟨.machine, 1, 2, 3, ⟨0, 0⟩, 4096, 2⟩),
  (0xfff0b193, .ITYPE (0xfff, .Regidx 1, .Regidx 3, .SLTIU), ⟨.machine, 1, 0, 3, ⟨65535, 65535⟩, 4096, 3⟩),
  (0x00208463, .BTYPE (8, .Regidx 2, .Regidx 1, .BEQ), ⟨.machine, 1, 2, 0, ⟨8, 0⟩, 24576, 0⟩),
  (0xffdff0ef, .JAL (0x1ffffc, .Regidx 1), ⟨.machine, 0, 0, 1, ⟨65532, 65535⟩, 1024, 0⟩),
  (0xfff08067, .JALR (0xfff, .Regidx 1, .Regidx 0), ⟨.machine, 1, 0, 0, ⟨65535, 65535⟩, 18432, 0⟩),
  (0x0020c1b3, .RTYPE (.Regidx 2, .Regidx 1, .Regidx 3, .XOR), ⟨.machine, 1, 2, 3, ⟨0, 0⟩, 65536, 52⟩),
  (0x0020e1b3, .RTYPE (.Regidx 2, .Regidx 1, .Regidx 3, .OR), ⟨.machine, 1, 2, 3, ⟨0, 0⟩, 65536, 53⟩),
  (0x0ff0f193, .ITYPE (0x0ff, .Regidx 1, .Regidx 3, .ANDI), ⟨.machine, 1, 0, 3, ⟨255, 0⟩, 65536, 54⟩),
  (0x01f09193, .SHIFTIOP (31, .Regidx 1, .Regidx 3, .SLLI), ⟨.machine, 1, 0, 3, ⟨31, 0⟩, 32768, 1⟩),
  (0x0020d1b3, .RTYPE (.Regidx 2, .Regidx 1, .Regidx 3, .SRL), ⟨.machine, 1, 2, 3, ⟨0, 0⟩, 32768, 2⟩),
  (0x41f0d193, .SHIFTIOP (31, .Regidx 1, .Regidx 3, .SRAI), ⟨.machine, 1, 0, 3, ⟨31, 0⟩, 32768, 3⟩)]

private theorem extraction (bits : BitVec 32) (instruction : SailRV32.instruction)
    (data : DecoderData UnifiedFamily)
    (decoded : run (SailRV32.Functions.encdec_backwards bits) (before bits) = .ok instruction (before bits))
    (fields : UnifiedReduced.decoderFields instruction = some data) :
    UnifiedReduced.programImage (before bits) [0] = some [⟨0, bits, instruction, data⟩] := by
  have bytes : (Cell.ram 0).read (before bits) = .ok bits (before bits) :=
    written_word_read default 0 bits
  simp only [List.mapM_cons, List.mapM_nil, programEntryRunWith, bytes, decoded, fields,
    bind, Option.bind, pure]

theorem all_instruction_forms : ∀ sample ∈ samples,
    UnifiedReduced.programImage (before sample.1) [0] = some [⟨0, sample.1, sample.2.1, sample.2.2⟩] := by
  intro sample member
  simp only [samples, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals apply extraction _ _ _ <;> with_unfolding_all rfl

private def xorEntry : UnifiedReduced.ProgramEntry :=
  ⟨0, 0x0020c1b3, .RTYPE (.Regidx 2, .Regidx 1, .Regidx 3, .XOR),
    ⟨.machine, 1, 2, 3, ⟨0, 0⟩, 65536, 52⟩⟩
private def xorRow : Nat → ZMod babyBearModulus
  | 5 => 1 | 6 => 2 | 7 => 3 | 10 => 52 | 27 => 1 | _ => 0

theorem native_query : UnifiedReduced.decoderQuery xorRow = xorEntry.query := by decide

theorem wrong_tag_rejected : ¬ (UnifiedReduced.decoderTable [xorEntry]).Contains #[]
    (UnifiedReduced.decoderQuery (fun i => if i = 10 then 4 else xorRow i)) := by
  intro member
  obtain ⟨entry, present, _, query⟩ := Proofs.decoder_member member
  simp only [List.mem_singleton] at present
  subst entry
  have tag := congrArg (fun q : Vector (ZMod babyBearModulus) 9 => q[7]) query
  exact (by decide : (4 : ZMod babyBearModulus) ≠ 52) tag

theorem wrong_selector_rejected : ¬ (UnifiedReduced.decoderTable [xorEntry]).Contains #[]
    (UnifiedReduced.decoderQuery (fun i => if i = 26 then 1 else xorRow i)) := by
  intro member
  obtain ⟨entry, present, _, query⟩ := Proofs.decoder_member member
  simp only [List.mem_singleton] at present
  subst entry
  have mask := congrArg (fun q : Vector (ZMod babyBearModulus) 9 => q[8]) query
  exact (by decide : (98304 : ZMod babyBearModulus) ≠ 65536) mask

end Tests.UnifiedDecoder
