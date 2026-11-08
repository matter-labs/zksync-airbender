module
public import Human.Helpers.Context.Registries.JumpBranchSlt
public import Slop.JumpBranchSlt.Timestamp
public import Slop.Trace.RowHistory
public import Slop.Trace.PC
public import Slop.Trace.LatestReads
public import Slop.Trace.MemoryHistory
public import Slop.JumpBranchSlt

@[expose] public section

namespace Airbender.JumpBranchSlt

@[simp] theorem trace_columns (kind : TraceKind) :
    Trace.CircuitLayout.columns kind = importedConstraintsTraceColumns := by rfl

@[simp] theorem trace_ports (kind : TraceKind) :
    Trace.CircuitLayout.ports kind = importedConstraintsMemoryPorts := by rfl

@[simp] theorem trace_decoder_columns (kind : TraceKind) :
    Trace.CircuitLayout.decoderColumns kind = importedConstraintsDecoderColumns := by rfl

@[simp] theorem trace_constraints [Fact p.Prime] (kind : TraceKind)
    (rom : Table (ZMod p) (fields 9)) :
    Trace.CircuitLayout.constraints kind rom = clockConstraints := by rfl

end Airbender.JumpBranchSlt

namespace Airbender.JumpBranchSlt.Proofs
open Trace

/-- The shared complete-path/latest-read proofs use these checked local laws;
    no jump-specific state or memory consistency premise is added. -/
instance [Fact p.Prime] : Trace.Proofs.ClockLaws TraceKind p where
  finalBound _ row h := final_clock_bound h
  advance hp inverse _ row h bound := by
    have core := Verification.holds_of_sublist h
      (List.sublist_append_left importedConstraints importedConstraintsTimestampLookups)
    obtain ⟨carry, bit, low, high⟩ := timestamp_equations inverse core
    have final := final_clock_bound h
    apply Trace.Proofs.increment hp bound final bit
    · simpa [Row.columns, importedConstraintsTraceColumns, decodeTimestamp, timestampBase,
        ZMod.natCast_zmod_val] using low
    · simpa [Row.columns, importedConstraintsTraceColumns, decodeTimestamp, timestampBase,
        ZMod.natCast_zmod_val] using high
  portsClocks _ := memory_clocks
  offsets _ := rfl
  effects hp inverse _ _ h inputs := clocks hp inverse h inputs

/-- The cleanup query enforces a four-byte aligned outgoing low limb for every
    mode. It does not bound the outgoing high limb. -/
theorem outgoing_pc_aligned {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w) importedConstraints) :
    (w 16).val % 4 = 0 := by
  have range := (local_ranges h).2.2.2
  have cleaned := (lookup_values hp h).2.2.2.2
  have small : (w 36).val - (w 36).val % 4 < p := by
    exact lt_of_le_of_lt (Nat.sub_le _ _) (by dsimp [Arithmetic.limbBase] at range; omega)
  rw [cleaned, ZMod.val_natCast, Nat.mod_eq_of_lt small]
  omega

/-- Public initial alignment and native matching discharge every row's PC
    alignment; only the actual public initial state is a boundary condition. -/
theorem trace_pc_alignment {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p)
    {trace : NativeTrace p} (accepted : Accepted trace)
    (initial : trace.initial.word.lo % 4 = 0) :
    (∀ row ∈ trace.rows, row.start.word.lo % 4 = 0 ∧ row.finish.word.lo % 4 = 0) ∧
      trace.terminal.word.lo % 4 = 0 := by
  have outputs : ∀ row ∈ trace.rows, row.finish.word.lo % 4 = 0 := by
    intro row member
    exact outgoing_pc_aligned hp (Verification.holds_of_sublist (accepted.constraints row member)
      (List.sublist_append_left importedConstraints importedConstraintsTimestampLookups))
  have incoming := Trace.Proofs.matched_incoming_property accepted
    (fun state => state.word.lo % 4 = 0) initial outputs
  refine ⟨?_, incoming _ List.mem_cons_self⟩
  intro row member
  exact ⟨incoming _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨row, member, rfl⟩)),
    outputs row member⟩

end Airbender.JumpBranchSlt.Proofs
