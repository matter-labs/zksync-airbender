module
public import Proven.VerifierBoundary

@[expose] public section

namespace Airbender.VerifierBoundary

/-- Cancel the common row-start contribution to identify the raw terminal tuple. -/
theorem terminal_state_soundness : TerminalStateSoundnessClaim := @Proofs.terminal_state

/-- The public u32 terminal PC gives two canonical native PC limbs. -/
theorem terminal_bound_soundness : TerminalBoundSoundnessClaim := by
  intro p _ hp initial terminal starts ends matched closure
  exact Proofs.terminal_bound hp matched closure

/-- A one-row logical path meets the verifier's terminal-state premises. -/
theorem terminal_state_satisfiable : TerminalStateSatisfiableClaim := by
  let statement : Statement := boot ⟨4, (8, 0)⟩
  let first := statement.initial.encode (p := babyBearModulus)
  let last := statement.terminal.encode (p := babyBearModulus)
  have matched : (first :: [last]).Perm (last :: [first]) := List.Perm.swap _ _ _
  exact ⟨first, last, [first], [last], statement, matched, ⟨rfl, matched⟩, by simp⟩

/-- The same path meets the terminal-bound premises. -/
theorem terminal_bound_satisfiable : TerminalBoundSatisfiableClaim := by
  obtain ⟨first, last, starts, ends, statement, matched, binding, nonempty⟩ := terminal_state_satisfiable
  exact ⟨first, last, starts, ends, by decide, matched, ⟨statement, binding⟩, nonempty⟩

end Airbender.VerifierBoundary
