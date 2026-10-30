import Airbender.Import.SetupSourceIndices
import Airbender.Proofs.FullUnsigned.SetupSourceArrays

namespace Airbender.Setup.SourceIndices
set_option warningAsError true
set_option Elab.async false

private theorem go_length (base count value : Nat) (earlier : List Nat) :
    (go base count value earlier).length = count + earlier.length := by
  induction count generalizing value earlier with
  | zero => simp [go]
  | succ count ih =>
    rw [go, ih, List.length_cons]
    omega

theorem decode_length (base count packed : Nat) : (decode base count packed).length = count := by
  simpa only [decode, List.length_nil, Nat.add_zero] using go_length base count packed []

private theorem go_last (base count value : Nat) (earlier : List Nat) :
    (go base (count + 1) value earlier).getLast? = some ((value / base ^ count) % base) := by
  induction count generalizing value earlier with
  | zero => simp [go]
  | succ count ih =>
    rw [go, ih, Nat.div_div_eq_div_mul, ← Nat.pow_succ']

theorem decode_last (base count packed : Nat) :
    (decode base (count + 1) packed).getLast? = some ((packed / base ^ count) % base) :=
  go_last base count packed []

end Airbender.Setup.SourceIndices
