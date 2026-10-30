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

private theorem go_prefix (base count value : Nat) (earlier : List Nat) :
    go base count value earlier = earlier.reverse ++ decode base count value := by
  induction count generalizing value earlier with
  | zero => simp [go, decode]
  | succ count ih =>
    change go base count (value / base) ((value % base) :: earlier) =
      earlier.reverse ++ go base count (value / base) [value % base]
    rw [ih, ih]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.append_assoc]

theorem decode_succ (base count packed : Nat) :
    decode base (count + 1) packed = packed % base :: decode base count (packed / base) := by
  change go base count (packed / base) [packed % base] = _
  rw [go_prefix]
  simp

/-- An exact source suffix follows from division of its packed index data. -/
theorem decode_drop (base first rest packed : Nat) :
    (decode base (first + rest) packed).drop first =
      decode base rest (packed / base ^ first) := by
  induction first generalizing packed with
  | zero => simp
  | succ first ih =>
    rw [Nat.succ_add, decode_succ, List.drop_succ_cons, ih,
      Nat.div_div_eq_div_mul, ← Nat.pow_succ']

end Airbender.Setup.SourceIndices
