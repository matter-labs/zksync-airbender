module
public import Proven.NonVacuous.RoundWindow.Model

@[expose] public section
namespace Airbender.NonVacuous.RoundWindow
open Trace Trace.Machine HashCallers
set_option warningAsError true

/-- All ten requests form one complete round protocol in the public interval. -/
theorem protocol_profile :
    HashWindowProfile ((List.range 10).map (requestAt .blakeRound 4)) windows := by
  constructor <;> decide +kernel

private theorem program_round {family : RVMachineDecoderFamily} {instruction : RVMachineProgramEntry}
    (member : instruction ∈ addresses.map (entry family)) :
    ∃ kind ∈ (HashProtocol.round false).kinds, RV.decode instruction.bits = some (.delegate kind) := by
  obtain ⟨address, _, rfl⟩ := List.mem_map.mp member
  refine ⟨.blakeRound, ?_, ?_⟩
  · exact List.mem_replicate.mpr ⟨by decide, rfl⟩
  · exact FamilyCallers.decode_caller .blakeRound

/-- Every unrolled public instruction in the interval is a round call. -/
theorem unrolled_scope : ∀ window ∈ windows, CodeWindowScope unrolledTrace unrolledProgram window := by
  intro window member
  have equal : window = ⟨.round false, 4, 44⟩ := List.mem_singleton.mp member
  subst window
  refine ⟨by decide +kernel, by decide +kernel, by decide, by decide, by decide, ?_⟩
  intro _ _ _ instruction present _
  exact program_round present

/-- Every unified public instruction in the interval is a round call. -/
theorem unified_scope : ∀ window ∈ windows, CodeWindowScope unifiedTrace unifiedProgram window := by
  intro window member
  have equal : window = ⟨.round false, 4, 44⟩ := List.mem_singleton.mp member
  subst window
  refine ⟨by decide +kernel, by decide +kernel, by decide, by decide, by decide, ?_⟩
  intro _ _ _ instruction present _
  exact program_round present

end Airbender.NonVacuous.RoundWindow
