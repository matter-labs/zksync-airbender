import Airbender.Review.Helpers.Context.PCState.Model

namespace Airbender.VerifierBoundary

/-- Typed statement words read by the total verifier. Timestamp limbs are u32
    words converted to the field with reduction; PC limbs use the u16 split. -/
structure Endpoint where
  pc : BitVec 32
  timestamp : BitVec 32 × BitVec 32

/-- Preserve both PC columns and both timestamp columns of the boundary tuple.
    The PC split is Rust's `num & 0xffff`, `num >> 16`; do not repack a raw tuple. -/
def Endpoint.encode {p : Nat} (endpoint : Endpoint) : PCState.State p :=
  PCState.boundary endpoint.pc (endpoint.timestamp.1.toNat, endpoint.timestamp.2.toNat)

structure Statement where
  initial : Endpoint
  terminal : Endpoint

/-- The inspected total-verifier paths use INITIAL_PC = 0 and INITIAL_TIMESTAMP = 4.
    Other canonical initial endpoints describe conditional trace/segment scopes. -/
def boot (terminal : Endpoint) : Statement := ⟨⟨0, (4, 0)⟩, terminal⟩

/-- External logical PC-space closure over the actual imported row tuples.
    `initial` binds the same initial contribution used by trace acceptance;
    `balanced` keeps each raw PC/timestamp column separately in the permutation.

    Source inspected at 0dc0a631349462700825f326516d36200be30edc:
    full_statement_verifier/src/unrolled_proof_statement.rs:76,241-253;
    full_statement_verifier/src/unified_circuit_statement.rs:74,249-261;
    prover/src/definitions/mod.rs:8-11,269-302;
    cs/src/gkr_compiler/memory_like_grand_product.rs:478-502.
    These two Rust paths read final PC as u32 and multiply its split PC-space
    contribution into global read/write product equality. Cryptographic soundness
    of that equality and correspondence of these lists to the Rust/artifact
    contributions remain external. Equality at sampled challenges is not a
    deterministic multiset-equality proof. No other verifier variant is claimed. -/
structure Binding {p : Nat} (initial : PCState.State p)
    (starts ends : List (PCState.State p)) (statement : Statement) : Prop where
  initial : initial = statement.initial.encode
  balanced : (statement.initial.encode :: ends).Perm (statement.terminal.encode :: starts)

/-- A typed statement and its logical boundary binding, with no terminal range premise. -/
def Closure {p : Nat} (initial : PCState.State p) (starts ends : List (PCState.State p)) : Prop :=
  ∃ statement, Binding initial starts ends statement

/-- Specialization to the inspected total-verifier initial contribution. -/
def BootClosure {p : Nat} (initial : PCState.State p) (starts ends : List (PCState.State p)) : Prop :=
  ∃ terminal, Binding initial starts ends (boot terminal)

end Airbender.VerifierBoundary
