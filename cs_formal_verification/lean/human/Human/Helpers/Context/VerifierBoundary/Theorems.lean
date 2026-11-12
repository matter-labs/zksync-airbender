module
public import Human.Helpers.Context.VerifierBoundary.Model
public import Human.Helpers.Context.Model
public import Human.Helpers.Memory.InitialImageRV
public import Human.Helpers.Core.BabyBearPrime

@[expose] public section

namespace Airbender.VerifierBoundary
open Trace

/-- Logical row matching and the verifier contribution identify the complete raw terminal tuple. -/
def TerminalStateSoundnessClaim : Prop :=
  ∀ {p : Nat} {initial terminal : PCState.State p} {starts ends : List (PCState.State p)}
    {statement : Statement},
    (initial :: ends).Perm (terminal :: starts) → Binding initial starts ends statement →
    terminal = statement.terminal.encode

/-- Typed full statement closure derives both terminal PC limb bounds. -/
def TerminalBoundSoundnessClaim : Prop :=
  ∀ {p : Nat} [Fact p.Prime], Arithmetic.limbBase < p →
    ∀ {initial terminal : PCState.State p} {starts ends : List (PCState.State p)},
    (initial :: ends).Perm (terminal :: starts) → Closure initial starts ends → terminal.word.Bounded

/-- The logical terminal-state premises hold for a nonempty row path. -/
def TerminalStateSatisfiableClaim : Prop :=
  ∃ (initial terminal : PCState.State babyBearModulus) (starts ends : List (PCState.State babyBearModulus))
    (statement : Statement),
    (initial :: ends).Perm (terminal :: starts) ∧ Binding initial starts ends statement ∧ starts ≠ []

/-- The logical terminal-bound premises hold for a nonempty row path. -/
def TerminalBoundSatisfiableClaim : Prop :=
  ∃ (initial terminal : PCState.State babyBearModulus) (starts ends : List (PCState.State babyBearModulus)),
    Arithmetic.limbBase < babyBearModulus ∧
    (initial :: ends).Perm (terminal :: starts) ∧ Closure initial starts ends ∧ starts ≠ []

end Airbender.VerifierBoundary
