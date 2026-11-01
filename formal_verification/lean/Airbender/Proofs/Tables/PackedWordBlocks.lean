import Airbender.Proofs.Tables.PackedSignedRun

namespace Airbender.Setup.Proofs.PackedWordBlocks
open PackedSignedRun
set_option warningAsError true

def payloadArray (radix length payload : Nat) : Array Nat :=
  Array.ofFn (fun index : Fin length => digit radix payload index.val)

theorem payload_roundtrip (radix length payload : Nat) (positive : 1 < radix)
    (bounded : payload < radix ^ length) :
    Nat.ofDigits radix (payloadArray radix length payload).toList = payload := by
  let padded := Nat.digitsAppend radix length payload
  have paddedLength : padded.length = length := Nat.length_digitsAppend positive _ bounded
  have paddedValue : Nat.ofDigits radix padded = payload := by
    simp [padded, Nat.digitsAppend, Nat.ofDigits_append_replicate_zero, Nat.ofDigits_digits]
  have same : (payloadArray radix length payload).toList = padded := by
    apply List.ext_getElem
    · simpa [payloadArray] using paddedLength.symm
    · intro index leftBound rightBound
      have raw := PackedRadix.extractDigitBase radix padded index (by omega)
        (fun value member => Nat.lt_of_mem_digitsAppend positive length value member) rightBound
      rw [paddedValue] at raw
      simpa only [Array.getElem_toList, payloadArray, Array.getElem_ofFn, digit] using raw
  rw [same, paddedValue]

structure Input where
  count : Nat
  stride : Int
  period : Nat
  payload : Nat

def Input.length (data : Input) : Nat := data.count * data.period
def Input.asRun (radix : Nat) (data : Input) : PackedSignedRun.Run :=
  ⟨data.count, data.stride, payloadArray radix data.period data.payload⟩
def checkDigits (radix : Nat) (predicate : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | count + 1, payload => predicate (payload % radix) && checkDigits radix predicate count (payload / radix)

theorem checkDigits_sound (radix : Nat) (predicate : Nat → Bool) (count payload : Nat)
    (checked : checkDigits radix predicate count payload = true) (index : Nat) (within : index < count) :
    predicate (digit radix payload index) = true := by
  induction count generalizing payload index with
  | zero => omega
  | succ count ih =>
    simp only [checkDigits, Bool.and_eq_true] at checked
    cases index with
    | zero => simpa [digit] using checked.1
    | succ index =>
      have result := ih (payload / radix) checked.2 index (by omega)
      simpa only [digit, pow_succ', Nat.div_div_eq_div_mul] using result

def Input.seedValid (radix : Nat) (data : Input) (value : Nat) : Bool :=
  decide (value < radix ∧
    0 ≤ (value : Int) + data.stride * ((data.count - 1 : Nat) : Int) ∧
    (value : Int) + data.stride * ((data.count - 1 : Nat) : Int) < radix)

def Input.valid (radix : Nat) (data : Input) : Bool :=
  decide (data.payload < radix ^ data.period) &&
    checkDigits radix (data.seedValid radix) data.period data.payload

theorem valid_parts (radix : Nat) (data : Input) (valid : data.valid radix = true) :
    data.payload < radix ^ data.period ∧ (data.asRun radix).valid radix = true := by
  simp only [Input.valid, Bool.and_eq_true, decide_eq_true_eq] at valid
  refine ⟨valid.1, ?_⟩
  apply Array.all_eq_true.mpr
  intro index within
  have bound : index < data.period := by simpa [Input.asRun, payloadArray] using within
  have result := checkDigits_sound radix (data.seedValid radix) data.period data.payload valid.2 index bound
  simpa only [Input.seedValid, Input.asRun, payloadArray, Array.getElem_ofFn] using result

def Input.packed (radix : Nat) (data : Input) : Nat :=
  if data.period = 0 then 0 else
  let standard := radix ^ data.period
  let extent := standard ^ data.count
  let geometric := (extent - 1) / (standard - 1)
  let moment := (data.count * extent + 1 - (geometric + extent)) / (standard - 1)
  ((data.payload : Int) * geometric +
    data.stride * (((standard - 1) / (radix - 1) : Nat) : Int) * moment).toNat

theorem input_length (radix : Nat) (data : Input) :
    (data.asRun radix).length = data.length := by
  simp [Input.asRun, Input.length, PackedSignedRun.Run.length, payloadArray]

theorem packed_eq (radix : Nat) (positive : 1 < radix) (data : Input)
    (valid : data.valid radix = true) :
    data.packed radix = (data.asRun radix).packedArithmetic radix := by
  have bounded : data.payload < radix ^ data.period := (valid_parts radix _ valid).1
  simp only [Input.packed, Input.asRun, PackedSignedRun.Run.packedArithmetic,
    payloadArray, Array.size_ofFn]
  rw [show Nat.ofDigits radix (Array.ofFn (fun index : Fin data.period => digit radix data.payload index.val)).toList =
    data.payload from payload_roundtrip radix data.period data.payload positive bounded]

theorem packed_digit (radix : Nat) (positive : 1 < radix) (data : Input)
    (valid : data.valid radix = true) (index : Nat) (within : index < data.length) :
    digit radix (data.packed radix) index = (data.asRun radix).value index := by
  rw [packed_eq radix positive data valid]
  exact PackedSignedRun.packedArithmetic_digit radix positive _ (valid_parts radix _ valid).2 index
    (by rwa [input_length])

inductive Code where
  | affine (length first : Nat) (stride : Int)
  | dense (length payload : Nat)
  | periodic (count : Nat) (stride : Int) (period payload : Nat)

def Code.decode (radix : Nat) : Code → Block
  | .affine length first stride => .affine length first stride
  | .dense length payload => .dense (payloadArray radix length payload)
  | .periodic count stride period payload => .periodic count stride (payloadArray radix period payload)
def Code.input : Code → Input
  | .affine length first stride => ⟨length, stride, 1, first⟩
  | .dense length payload => ⟨1, 0, length, payload⟩
  | .periodic count stride period payload => ⟨count, stride, period, payload⟩
def Code.length (block : Code) : Nat := block.input.length

def ofBlock : Block → PackedSignedRun.Run
  | .affine count first stride => ⟨count, stride, #[first]⟩
  | .dense values => ⟨1, 0, values⟩
  | .periodic count stride values => ⟨count, stride, values⟩

theorem ofBlock_sound (radix : Nat) (block : Block)
    (valid : (ofBlock block).valid radix = true) :
    block.length = (ofBlock block).length ∧
      ∀ index, index < block.length → block.get? index = some ((ofBlock block).value index) := by
  cases block with
  | affine count first stride =>
    constructor
    · simp [Block.length, ofBlock, PackedSignedRun.Run.length]
    · intro index within
      change index < count at within
      have nonnegative : 0 ≤ (first : Int) + stride * index := by
        have bounds := value_bounds radix _ valid index (by simpa [ofBlock] using within)
          first (by simp [ofBlock])
        simpa [ofBlock] using bounds.1
      simp [Block.get?, Block.length, within, ofBlock, PackedSignedRun.Run.value, nonnegative, Nat.mod_one]
  | dense values =>
    constructor
    · simp [Block.length, ofBlock, PackedSignedRun.Run.length]
    · intro index within
      simp only [Block.length] at within
      simp [Block.get?, Block.length, within, ofBlock, PackedSignedRun.Run.value,
        Nat.mod_eq_of_lt within]
  | periodic count stride values =>
    constructor
    · rfl
    · intro index within
      have periodPositive : 0 < values.size := by simp only [Block.length] at within; nlinarith
      have rowWithin : index / values.size < count :=
        (Nat.div_lt_iff_lt_mul periodPositive).mpr (by simpa [Block.length, Nat.mul_comm] using within)
      have columnWithin := Nat.mod_lt index periodPositive
      have member : values[index % values.size]?.getD 0 ∈ values.toList := by
        simp [Array.getElem?_eq_getElem columnWithin]
      have nonnegative := (value_bounds radix _ valid _ rowWithin _ member).1
      simpa [Block.get?, within, ofBlock, PackedSignedRun.Run.value] using
        (if_pos nonnegative : (if 0 ≤ ((values[index % values.size]?.getD 0 : Nat) : Int) +
          stride * ((index / values.size : Nat) : Int) then
          some (((values[index % values.size]?.getD 0 : Nat) : Int) +
            stride * ((index / values.size : Nat) : Int)).toNat else none) = _)

theorem decode_length (radix : Nat) (block : Code) : (block.decode radix).length = block.length := by
  cases block <;> simp [Code.decode, Code.length, Code.input, Input.length, Block.length, payloadArray]

theorem input_raw (radix : Nat) (block : Code) (valid : block.input.valid radix = true) :
    ofBlock (block.decode radix) = block.input.asRun radix := by
  cases block with
  | affine length first stride =>
    have bound : first < radix := by
      have stored := (valid_parts radix _ valid).1
      simpa [Code.input] using stored
    have same : payloadArray radix 1 first = #[first] := by
      apply Array.ext (by simp [payloadArray])
      intro index leftBound rightBound
      have zero : index = 0 := by simpa [payloadArray] using leftBound
      subst index
      simp [payloadArray, digit, Nat.mod_eq_of_lt bound]
    simp [Code.decode, Code.input, ofBlock, Input.asRun, same]
  | dense length payload => rfl
  | periodic count stride period payload => rfl

theorem input_sound (radix : Nat) (positive : 1 < radix) (block : Code)
    (valid : block.input.valid radix = true) (index : Nat) (within : index < block.length) :
    (block.decode radix).get? index = some (digit radix (block.input.packed radix) index) := by
  have raw := ofBlock_sound radix (block.decode radix)
    (by rw [input_raw radix block valid]; exact (valid_parts radix _ valid).2)
  rw [input_raw radix block valid] at raw
  have result := raw.2 index (by rwa [decode_length])
  rw [← packed_digit radix positive block.input valid index within] at result
  exact result

end Airbender.Setup.Proofs.PackedWordBlocks
