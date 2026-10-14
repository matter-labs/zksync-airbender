import Airbender.Review.Helpers.Context.VerifierBoundary.Model
import Airbender.Review.Helpers.Context.Model
import Airbender.Review.Helpers.Memory.InitialImage
import Airbender.Proofs.PCState
import Airbender.Proofs.Arithmetic.Word

namespace Airbender.VerifierBoundary.Proofs

theorem encoded_word {p : Nat} (hp : Arithmetic.limbBase < p) (endpoint : Endpoint) :
    (endpoint.encode (p := p)).word = Arithmetic.Word.ofBitVec endpoint.pc := by
  have lo := Nat.mod_lt endpoint.pc.toNat (by decide : 0 < Arithmetic.limbBase)
  have hi := (Arithmetic.Word.ofBitVec_bound endpoint.pc).2
  change endpoint.pc.toNat / Arithmetic.limbBase < Arithmetic.limbBase at hi
  dsimp [Endpoint.encode, PCState.boundary, PCState.encode, PCState.State.word, Arithmetic.Word.ofBitVec]
  rw [ZMod.val_natCast_of_lt (by omega : endpoint.pc.toNat % Arithmetic.limbBase < p),
    ZMod.val_natCast_of_lt (by omega : endpoint.pc.toNat / Arithmetic.limbBase < p)]

theorem encoding_soundness {p : Nat} (hp : Arithmetic.limbBase < p) (endpoint : Endpoint) :
    (endpoint.encode (p := p)).word.Bounded ∧ (endpoint.encode (p := p)).word.toBitVec = endpoint.pc := by
  rw [encoded_word hp endpoint]
  exact ⟨Arithmetic.Word.ofBitVec_bound endpoint.pc, Arithmetic.Word.ofBitVec_roundtrip endpoint.pc⟩

/-- Cancel the identical start-list from the two state permutations. The result
    is equality of the full original terminal tuple, before any PC interpretation. -/
theorem terminal_state {p : Nat} {initial terminal : PCState.State p}
    {starts ends : List (PCState.State p)} {statement : Statement}
    (accepted : (initial :: ends).Perm (terminal :: starts))
    (binding : Binding initial starts ends statement) : terminal = statement.terminal.encode := by
  have same := accepted.symm.trans (binding.initial.symm ▸ binding.balanced)
  change ([terminal] ++ starts).Perm ([statement.terminal.encode] ++ starts) at same
  have singleton := (List.perm_append_right_iff starts).mp same
  simpa using List.perm_singleton.mp singleton

theorem binding_of_endpoints {p : Nat} {initial terminal : PCState.State p}
    {starts ends : List (PCState.State p)} {statement : Statement}
    (first : initial = statement.initial.encode) (last : terminal = statement.terminal.encode)
    (accepted : (initial :: ends).Perm (terminal :: starts)) : Binding initial starts ends statement :=
  ⟨first, by simpa only [← first, ← last] using accepted⟩

theorem boot_closure {p : Nat} {initial : PCState.State p} {starts ends : List (PCState.State p)}
    (binding : BootClosure initial starts ends) : Closure initial starts ends := by
  obtain ⟨terminal, binding⟩ := binding
  exact ⟨boot terminal, binding⟩

theorem terminal_bound {p : Nat} (hp : Arithmetic.limbBase < p) {initial terminal : PCState.State p}
    {starts ends : List (PCState.State p)} (accepted : (initial :: ends).Perm (terminal :: starts))
    (closure : Closure initial starts ends) : terminal.word.Bounded := by
  obtain ⟨statement, binding⟩ := closure
  rw [terminal_state accepted binding]
  exact (encoding_soundness hp statement.terminal).1

theorem trace_terminal_bound {Kind : Type} [Trace.CircuitLayout Kind] {p : Nat} [Fact p.Prime]
    (hp : Arithmetic.limbBase < p) {trace : Trace.Data p Kind} (accepted : Trace.Accepted trace)
    (closure : Closure trace.initial (trace.rows.map Trace.Row.start) (trace.rows.map Trace.Row.finish)) :
    trace.terminal.word.Bounded := terminal_bound hp accepted.states closure

end Airbender.VerifierBoundary.Proofs
