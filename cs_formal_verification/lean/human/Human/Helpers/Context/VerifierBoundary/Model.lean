module
public import Human.Helpers.Context.PCState.Model

@[expose] public section

namespace Airbender.VerifierBoundary

/-- Typed words of the full statement verifier's boundary contribution. -/
structure Endpoint where
  /-- The public 32-bit instruction address. -/
  pc : BitVec 32
  /-- The public timestamp words, reduced into the field separately. -/
  timestamp : BitVec 32 × BitVec 32

/-- Keep both PC limbs and both timestamp columns. -/
def Endpoint.encode {p : Nat} (endpoint : Endpoint) : PCState.State p :=
  PCState.boundary endpoint.pc (endpoint.timestamp.1.toNat, endpoint.timestamp.2.toNat)

/-- The public initial and terminal contributions. -/
structure Statement where
  /-- The initial contribution. -/
  initial : Endpoint
  /-- The terminal contribution. -/
  terminal : Endpoint

/-- The full statement verifier starts at PC zero and timestamp four. -/
def boot (terminal : Endpoint) : Statement := ⟨⟨0, (4, 0)⟩, terminal⟩

/-- Logical closure of the raw PC-space contributions. Cryptographic enforcement is external.
    The verifier splits its public u32 PC into two u16 limbs. It reduces each timestamp word separately. -/
structure Binding {p : Nat} (initial : PCState.State p)
    (starts ends : List (PCState.State p)) (statement : Statement) : Prop where
  /-- The initial tuple is the verifier's initial contribution. -/
  initial : initial = statement.initial.encode
  /-- The four raw columns balance with the verifier's terminal contribution. -/
  balanced : (statement.initial.encode :: ends).Perm (statement.terminal.encode :: starts)

/-- A typed public statement closes the raw native contribution lists. -/
def Closure {p : Nat} (initial : PCState.State p) (starts ends : List (PCState.State p)) : Prop :=
  ∃ statement, Binding initial starts ends statement

/-- The inspected full statement verifier's boot contribution closes the raw lists. -/
def BootClosure {p : Nat} (initial : PCState.State p) (starts ends : List (PCState.State p)) : Prop :=
  ∃ terminal, Binding initial starts ends (boot terminal)

end Airbender.VerifierBoundary
