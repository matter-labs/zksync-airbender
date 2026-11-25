module
public import Proven.UnifiedReduced.Standard.Profile
public import Proven.UnifiedReduced.MemoryMap
public import Proven.Final.Compiler.PermutationMachine
public import Proven.Final.Trace.UnifiedReduced.Proth120Padding

@[expose] public section
namespace Airbender.UnifiedReduced.Standard
open Trace Trace.Machine Compiler PaddingBoundary
set_option backward.isDefEq.respectTransparency false

abbrev Profile.Kind : Profile → Type
  | .babyBear => UnifiedFamily
  | .proth120 => Proth120.Kind

noncomputable instance (profile : Profile) : CircuitLayout profile.Kind := match profile with
  | .babyBear => inferInstanceAs (CircuitLayout UnifiedFamily)
  | .proth120 => inferInstanceAs (CircuitLayout Proth120.Kind)

abbrev Profile.Submission (profile : Profile) := Data profile.modulus profile.Kind

noncomputable def consumed : (profile : Profile) → profile.Submission → Nat
  | .babyBear, trace => unifiedReadCount (active trace)
  | .proth120, trace => ExternalStream.count Proth120.isRead (active trace).rows

/-- The native premises of each compiled target. BabyBear carries its worker pools, boot
    and public tables; wrap carries its row assignments, public setup, and a CPU-only permutation. -/
inductive NativeEvidence : (profile : Profile) → profile.Submission → RV.State → List Cell → Prop
  | babyBear {trace : UnifiedTrace babyBearModulus} {workers initial cells program inits tables}
      {E : Type} [CommRing E] {challenges : NativeMemory.Challenges E}
      {certificates : List (UnifiedRowCertificate tables)} {values : List (GKRAddress → E)}
      (boot : BootInputs .unified (active trace) initial cells program InitsTeardowns.unifiedLayout inits)
      (instructions : NoSpecial5 program) (stream : UnifiedStreamPorts (active trace) initial.input)
      (setup : NativePublicSetup.Bound initial program tables)
      (gates : PaddedUnifiedPermutationArguments challenges tables certificates values trace workers) :
      NativeEvidence .babyBear trace initial cells
  | proth120 {trace : Proth120.WrapTrace} {initial cells} (gates : Proth120.PaddedInputs trace initial cells) :
      NativeEvidence .proth120 trace initial cells

/-- Either compiled unified machine executes from its public RV state with its own ROM
    boundary. The final stream suffix, PC, and all tracked terminal register/RAM values agree. -/
theorem native_execution {profile trace initial cells} (evidence : NativeEvidence profile trace initial cells) :
    ∃ n, RealizesRun trace initial cells (consumed profile trace) (RV.runAt (profile.romLimbs * 65536) n initial) := by
  cases evidence with
  | babyBear boot instructions stream setup gates =>
    obtain ⟨n, run⟩ := Machine.Native.padded_unified_from_native_permutation _ _ _ _ _ _ _
      boot instructions stream setup _ _ _ gates
    refine ⟨n, ?_⟩
    rw [show Profile.babyBear.romLimbs * 65536 = RV.ROM_END by rfl, RV.runAt_default]
    exact run
  | proth120 gates =>
    exact ⟨_, Proth120.padded_trace_soundness _ _ _ gates⟩

/-- Each target admits an actual native submission containing one active and one padding row. -/
theorem native_execution_satisfiable (profile : Profile) :
    ∃ (t : profile.Submission) (initial : RV.State) (cells : List Cell), NativeEvidence profile t initial cells ∧
      (active t).rows.length = 1 ∧ (inactive t).rows.length = 1 := by
  cases profile with
  | babyBear =>
    obtain ⟨trace, _, initial, cells, _, _, _, boot, instructions, stream, setup, _, _, _, gates, yes, no⟩ :=
      Machine.Native.padded_unified_from_native_permutation_satisfiable
    exact ⟨trace, initial, cells, .babyBear boot instructions stream setup gates, yes, no⟩
  | proth120 =>
    obtain ⟨trace, initial, cells, gates, _, yes, no⟩ := Proth120.padded_trace_soundness_satisfiable
    exact ⟨trace, initial, cells, .proth120 gates, yes, no⟩

end Airbender.UnifiedReduced.Standard
