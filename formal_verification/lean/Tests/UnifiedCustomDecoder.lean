import Airbender.Proofs.UnifiedReduced.CustomDecoder
import Airbender.Proofs.Sail.WordMemoryState

namespace Tests.UnifiedCustomDecoder
open Airbender UnifiedReduced Trace Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

private def encoding (kind : Fin 5) : BitVec 32 :=
  (#v[0xc27342f3, 0xc1c342f3, 0x8dc342f3, 0x89c342f3, 0x85f342f3] : Vector (BitVec 32) 5)[kind]

private def instruction (kind : Fin 5) : SailRV32.instruction :=
  if kind = 0 then .ZIMOP_MOP_RR (4, .Regidx 7, .Regidx 6, .Regidx 5)
  else .ZIMOP_MOP_R ((#v[0, 16, 12, 8, 7] : Vector (BitVec 5) 5)[kind], .Regidx 6, .Regidx 5)

private def entry (kind : Fin 5) : UnifiedReduced.ProgramEntry :=
  ⟨0, encoding kind, instruction kind,
    if kind = 0 then ⟨.machine, 6, 7, 5, ⟨0, 0⟩, 512, 0⟩
    else ⟨.machine, 6, 5, 5, ⟨0, 0⟩, 65536, 46 + kind.val⟩⟩

theorem original_decoder_pure (kind : Fin 5) :
    SailRV32.Functions.encdec_backwards (encoding kind) =
      (.pure (instruction kind) : SailRV32.SailM SailRV32.instruction) := by
  fin_cases kind <;> with_unfolding_all rfl

theorem original_decoder (kind : Fin 5) (state : State) :
    run (SailRV32.Functions.encdec_backwards (encoding kind)) state =
      .ok (instruction kind) state := by
  rw [original_decoder_pure]
  rfl

theorem native_metadata (kind : Fin 5) :
    customDecoderFields (instruction kind) = some (entry kind).data := by
  fin_cases kind <;> rfl

theorem old_destination (kind : Fin 5) (xorrot : kind ≠ 0) :
    (entry kind).data.rs2 = (entry kind).data.rd := by
  fin_cases kind <;> first | contradiction | rfl

private def before (kind : Fin 5) : State :=
  wordWriteState default 0 (encoding kind)

theorem public_image (kind : Fin 5) :
    customProgramImage (before kind) [0] = some [entry kind] := by
  have bytes : (Cell.ram 0).read (before kind) = .ok (encoding kind) (before kind) :=
    written_word_read default 0 (encoding kind)
  have decoded := original_decoder kind (before kind)
  have fields := native_metadata kind
  simp only [List.mapM_cons, List.mapM_nil, programEntryRunWith, bytes, decoded, fields,
    bind, Option.bind, pure]
  rfl

theorem unsupported_rejected :
    customDecoderFields (.ZIMOP_MOP_RR (3, .Regidx 7, .Regidx 6, .Regidx 5)) = none ∧
    customDecoderFields (.ZIMOP_MOP_R (1, .Regidx 6, .Regidx 5)) = none ∧
    customDecoderFields (.ZIMOP_MOP_RR (4, .Regidx 7, .Regidx 6, .Regidx 0)) = none ∧
    customDecoderFields (.ZIMOP_MOP_R (16, .Regidx 6, .Regidx 0)) = none := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem standard_claim_excludes_custom (kind : Fin 5) :
    UnifiedReduced.decoderFields (instruction kind) = none := by
  fin_cases kind <;> rfl

end Tests.UnifiedCustomDecoder
