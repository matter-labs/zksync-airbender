import Human.ISA.RV32

/-! The interface to the delegation CSR table (`DelegationKind.ofCsr`): a decoded kind's CSR is the one in the word.
Proofs use only this lemma, never the table, so adding a CSR re-proves nothing downstream. -/

namespace RV

theorem ofCsr_csr {c : BitVec 12} {k : DelegationKind} (h : DelegationKind.ofCsr c = some k) : k.csr = c := by
  unfold DelegationKind.ofCsr at h
  split_ifs at h <;> cases h <;> subst_vars <;> rfl

end RV
