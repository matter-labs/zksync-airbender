module
public import Tests.JumpHistory
public import Proven.JumpBranchSlt.WitnessCheck
public import Proven.NonVacuous.SingleRow
public import Proven.Final.Helpers.Context.VerifierBoundary.Theorems
public import Human.Circuits.JumpBranchSlt.RVDecoder
public import Human.Trace.Families.JumpBranchSlt.RVTheorems

@[expose] public section

namespace Tests.VerifierBoundary
open Airbender Arithmetic Trace
set_option maxRecDepth 16384

/-- JAL x1,-4 with the high-PC wrap bit set and its field-aliased terminal high limb. -/
def assignment (i : Nat) : ZMod babyBearModulus :=
  if i = 17 then -1 else if i = 40 then 1 else Tests.JumpHistory.assignment 5 false i

def row : Row babyBearModulus JumpBranchSlt.TraceKind := ⟨.jumpBranchSlt, assignment⟩

def trace : JumpBranchSlt.NativeTrace babyBearModulus :=
  { Tests.JumpHistory.trace 5 false (ROM.table [] []) with rows := [row], terminal := row.finish }

/-- The exact imported native constraints accept the malformed terminal PC. -/
theorem satisfies : FlatOperation.ConstraintsHoldFlat (Verification.environment assignment)
    JumpBranchSlt.clockConstraints :=
  JumpBranchSlt.holds_of_check (by kernel_rfl) (by kernel_rfl)

/-- The raw native state and memory permutations also accept this row. -/
theorem noncanonical_native_accepted : Accepted trace :=
  Airbender.NonVacuous.accepted_of_row rfl satisfies rfl (by kernel_rfl) rfl (by decide +kernel)

/-- The public state holds JAL x1,-4 at PC zero and the actual register seeds. -/
def initial : RV.State where
  pc := 0
  regFile index := if index = 1 then 5 else 0
  rom address := match address.toNat with
    | 0 => 0xef
    | 1 => 0xf0
    | 2 => 0xdf
    | 3 => 0xff
    | _ => 0
  mem _ := 0

def program : List JumpBranchSlt.RVProgramEntry :=
  [⟨0, 0xffdff0ef#32, ⟨(), 0, 0, 1, ⟨65532, 65535⟩, 1, 0⟩⟩]

/-- The public ROM bytes construct the native query metadata. -/
theorem noncanonical_program_image :
    rvProgramImageWith JumpBranchSlt.rvDecoderFields initial [0] = some program := by
  kernel_rfl

/-- The native initial tokens are reads of the public state. -/
theorem noncanonical_initial_image :
    initialImageRV initial [.register 0, .register 1] = some trace.initialMemory := by
  kernel_rfl

/-- The incoming JAL query is a member of the public RV decoder table. -/
theorem noncanonical_decoded : JumpBranchSlt.RVDecoded trace program := by
  intro actual member
  simp only [trace, List.mem_singleton] at member
  subst actual
  exact ⟨⟨0, by decide +kernel⟩, by kernel_rfl⟩

/-- Its high terminal limb is not canonical. -/
theorem noncanonical_terminal_unbounded : ¬ trace.terminal.word.Bounded := by
  change ¬ (⟨65532, (-1 : ZMod babyBearModulus).val⟩ : Word).Bounded
  intro bounded
  exact (by decide +kernel : ¬ (-1 : ZMod babyBearModulus).val < limbBase) bounded.2

/-- No typed verifier contribution can close the same raw state permutation. -/
theorem noncanonical_verifier_boundary_rejected :
    ¬ Airbender.VerifierBoundary.Closure trace.initial (trace.rows.map Row.start) (trace.rows.map Row.finish) := by
  intro closure
  exact noncanonical_terminal_unbounded
    (Airbender.VerifierBoundary.Proofs.trace_terminal_bound (by decide +kernel) noncanonical_native_accepted closure)

end Tests.VerifierBoundary
