import Airbender.Review.Trace.Families.ReducedMachine.ArithmeticValues
import Airbender.Review.Trace.Families.ReducedMachine.ArithmeticResults

namespace Tests.NativeReducedArithmeticValues
open Airbender Trace ReducedMachine Native
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Initialized native source ranges are consequences, including the unchecked
    low source limb; no source value/range input is supplied. -/
theorem oversized_source_rejected {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup ArithmeticMode} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : arithmeticDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace)
    (decoded : ArithmeticDecodedTrace trace setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ trace.rows) :
    (sourceWord row.assignment).lo < 65536 := by
  have ranges := (public_arithmetic_value_bounds image inputs accepted decoded).1 row present
  cases row with
  | mk family w =>
    cases family
    have first := ranges importedConstraintsMemoryPorts[0] (by
      change _ ∈ importedConstraintsMemoryPorts; simp [importedConstraintsMemoryPorts])
    rw [Trace.Proofs.read_word] at first
    exact first.1

/-- Actual decoded x0 destinations have canonical zero writes, while their
    candidate and all readonly inputs continue to participate in acceptance. -/
theorem initialized_discarded_write {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup ArithmeticMode} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : arithmeticDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace)
    (decoded : ArithmeticDecodedTrace trace setup)
    (row : Row mersenne31Modulus NativeReducedFamily) (present : row ∈ trace.rows)
    (zero : rdIndex row.assignment = 0) : writtenWord row.assignment = ⟨0,0⟩ := by
  obtain ⟨entry,_,_,_,fields,_,written⟩ := public_arithmetic_results image inputs accepted decoded row present
  have bound := entry.data.rd.isLt
  have small : entry.data.rd.toNat < mersenne31Modulus := by change _ < 2147483647; omega
  have natural := congrArg ZMod.val fields.rd
  rw [zero,ZMod.val_zero,ZMod.val_natCast_of_lt small] at natural
  have index : entry.data.rd = 0 := by apply BitVec.eq_of_toNat_eq; simpa using natural.symm
  simpa only [index,if_true] using written

/-- Every actual terminal word remains bounded through initialized native matching. -/
theorem oversized_terminal_rejected {trace : Data mersenne31Modulus NativeReducedFamily}
    {setup : SparseDecoderSetup ArithmeticMode} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {count logCapacity : Nat}
    (image : arithmeticDecoderSetupImage before count logCapacity = some setup)
    (inputs : ImageBoundary trace before cells) (accepted : Accepted trace)
    (decoded : ArithmeticDecodedTrace trace setup) {token : MemoryToken mersenne31Modulus}
    (present : token ∈ trace.terminalMemory) : token.word.lo < 65536 :=
  ((public_arithmetic_value_bounds image inputs accepted decoded).2.2 token present).1

end Tests.NativeReducedArithmeticValues
