import Airbender.Proofs.Tables.PackedWordBounds

namespace Airbender.Setup.Proofs.PackedWordColumn
open PackedSignedRun PackedWordBlocks PackedWordBounds
set_option warningAsError true

def wordPower (count : Nat) : Nat := 65536 ^ count

theorem wordPower_eq (count : Nat) : wordPower count = 65536 ^ count := rfl

theorem run_packed_bound (data : PackedSignedRun.Run) (valid : data.valid 65536 = true)
    (positive : 0 < data.length) : data.packed 65536 < 65536 ^ data.length := by
  have periodPositive : 0 < data.values.size := by unfold PackedSignedRun.Run.length at positive; nlinarith
  have rowBounds : ∀ value ∈ (List.range data.count).map (data.row 65536),
      value < 65536 ^ data.values.size := by
    intro value member
    obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp member
    have bound := Nat.ofDigits_lt_base_pow_length (b := 65536)
      (l := data.values.toList.map (fun (value : Nat) => ((value : Int) + data.stride * row).toNat))
      (by omega) (by
        intro shifted shiftedMember
        obtain ⟨raw, rawMember, rfl⟩ := List.mem_map.mp shiftedMember
        have limits := value_bounds 65536 data valid row (List.mem_range.mp rowMember) raw rawMember
        omega)
    simpa [PackedSignedRun.Run.row] using bound
  have total := Nat.ofDigits_lt_base_pow_length (b := 65536 ^ data.values.size)
    (l := (List.range data.count).map (data.row 65536))
    (one_lt_pow₀ (by omega) (by omega)) rowBounds
  simpa only [List.length_map, List.length_range, ← pow_mul, Nat.mul_comm,
    PackedSignedRun.Run.packed, PackedSignedRun.Run.length] using total

theorem input_packed_bound (data : Input) (valid : fastValid data = true)
    (positive : 0 < data.length) : data.packed 65536 < 65536 ^ data.length := by
  have checked := valid_parts 65536 data (fastValid_sound data valid)
  have nonempty : 0 < (data.asRun 65536).values.size := by
    have codeLength := input_length 65536 data
    simp only [PackedSignedRun.Run.length] at codeLength
    nlinarith
  rw [packed_eq 65536 (by omega) data (fastValid_sound data valid),
    packedArithmetic_eq 65536 (by omega) _ checked.2 nonempty]
  rw [← input_length 65536 data]
  exact run_packed_bound _ checked.2 (by rwa [input_length])

def codeLength (blocks : List Code) : Nat := (blocks.map Code.length).sum

def packed : List Code → Nat
  | [] => 0
  | block :: rest => block.input.packed 65536 + wordPower block.length * packed rest

def valid (blocks : List Code) : Bool :=
  blocks.all (fun block => fastValid block.input && decide (0 < block.length))

theorem concat_bound (left right leftLength rightLength : Nat)
    (leftBound : left < 65536 ^ leftLength) (rightBound : right < 65536 ^ rightLength) :
    left + wordPower leftLength * right < 65536 ^ (leftLength + rightLength) := by
  rw [wordPower_eq, pow_add]
  have positive : 0 < 65536 ^ leftLength := by positivity
  nlinarith

theorem concat_low (left right count index : Nat) (bounded : left < 65536 ^ count)
    (within : index < count) :
    digit 65536 (left + wordPower count * right) index = digit 65536 left index := by
  have reduced : (left + wordPower count * right) % 65536 ^ count = left := by
    simp only [wordPower_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt bounded]
  have projected := segment_digit 65536 (left + wordPower count * right) 0 count index within
  simp only [pow_zero, Nat.div_one, Nat.zero_add, reduced] at projected
  exact projected.symm

theorem concat_high (left right count index : Nat) (bounded : left < 65536 ^ count) :
    digit 65536 (left + wordPower count * right) (count + index) = digit 65536 right index := by
  have divided : (left + wordPower count * right) / 65536 ^ count = right := by
    simp only [wordPower_eq, Nat.add_mul_div_left _ _ (show 0 < 65536 ^ count by positivity),
      Nat.div_eq_of_lt bounded, Nat.zero_add]
  unfold digit
  rw [pow_add, ← Nat.div_div_eq_div_mul, divided]

theorem packed_bound (blocks : List Code) (checked : valid blocks = true) :
    packed blocks < 65536 ^ codeLength blocks := by
  induction blocks with
  | nil => decide +kernel
  | cons block rest ih =>
    simp only [valid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at checked
    have first : block.input.packed 65536 < 65536 ^ block.length :=
      input_packed_bound block.input checked.1.1 checked.1.2
    have tail := ih checked.2
    simpa only [packed, codeLength, List.map_cons, List.sum_cons] using
      concat_bound _ _ _ _ first tail

theorem packed_sound (blocks : List Code) (checked : valid blocks = true)
    (index : Nat) (within : index < codeLength blocks) :
    getFromBlocks (blocks.map (Code.decode 65536)) index = some (digit 65536 (packed blocks) index) := by
  induction blocks generalizing index with
  | nil => simp [codeLength] at within
  | cons block rest ih =>
    simp only [valid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at checked
    have bounded : block.input.packed 65536 < 65536 ^ block.length :=
      input_packed_bound block.input checked.1.1 checked.1.2
    simp only [List.map_cons, getFromBlocks, decode_length]
    split
    next inside =>
      rw [packed, concat_low _ _ _ _ bounded inside]
      exact input_sound 65536 (by omega) block (fastValid_sound block.input checked.1.1) index inside
    next outside =>
      have tailBound : index - block.length < codeLength rest := by
        change index < block.length + codeLength rest at within
        omega
      have result := ih checked.2 (index - block.length) tailBound
      have projected := concat_high _ (packed rest) _ (index - block.length) bounded
      rw [show block.length + (index - block.length) = index from by omega] at projected
      rw [packed, projected]
      exact result

theorem decoded_length (blocks : List Code) :
    ((blocks.map (Code.decode 65536)).map Block.length).sum = codeLength blocks := by
  simp only [codeLength, List.map_map, Function.comp_def, decode_length]

theorem getFromBlocks_append_left (left right : List Block) (index : Nat)
    (within : index < (left.map Block.length).sum) :
    getFromBlocks (left ++ right) index = getFromBlocks left index := by
  induction left generalizing index with
  | nil => simp at within
  | cons block rest ih =>
    simp only [List.map_cons, List.sum_cons] at within
    simp only [List.cons_append, getFromBlocks]
    by_cases first : index < block.length
    · simp only [if_pos first]
    · simp only [if_neg first]
      exact ih (index - block.length) (by omega)

theorem getFromBlocks_append_right (left right : List Block) (index : Nat)
    (within : (left.map Block.length).sum ≤ index) :
    getFromBlocks (left ++ right) index = getFromBlocks right (index - (left.map Block.length).sum) := by
  induction left generalizing index with
  | nil => simp
  | cons block rest ih =>
    simp only [List.map_cons, List.sum_cons] at within ⊢
    have outside : ¬index < block.length := by omega
    simp only [List.cons_append, getFromBlocks, if_neg outside]
    rw [ih (index - block.length) (by omega)]
    congr 1
    omega

inductive Tree where
  | leaf (blocks : List Code) (count payload : Nat)
  | branch (left right : Tree)

def Tree.blocks : Tree → List Code
  | .leaf blocks _ _ => blocks
  | .branch left right => left.blocks ++ right.blocks

def Tree.length : Tree → Nat
  | .leaf _ count _ => count
  | .branch left right => left.length + right.length

def Tree.payload : Tree → Nat
  | .leaf _ _ payload => payload
  | .branch left right => left.payload + wordPower left.length * right.payload

def Tree.check : Tree → Bool
  | .leaf blocks count payload => valid blocks && codeLength blocks == count && packed blocks == payload
  | .branch left right => left.check && right.check

theorem Tree.check_sound (data : Tree) (checked : data.check = true) :
    data.length = codeLength data.blocks ∧ data.payload < 65536 ^ data.length ∧
      ∀ index < data.length, getFromBlocks (data.blocks.map (Code.decode 65536)) index =
        some (digit 65536 data.payload index) := by
  induction data with
  | leaf blocks count payload =>
    simp only [Tree.check, Bool.and_eq_true, beq_iff_eq] at checked
    obtain ⟨⟨valid, sameLength⟩, samePayload⟩ := checked
    subst count
    subst payload
    exact ⟨rfl, packed_bound blocks valid, packed_sound blocks valid⟩
  | branch left right leftIH rightIH =>
    simp only [Tree.check, Bool.and_eq_true] at checked
    obtain ⟨leftLength, leftBound, leftSound⟩ := leftIH checked.1
    obtain ⟨rightLength, rightBound, rightSound⟩ := rightIH checked.2
    refine ⟨?_, concat_bound _ _ _ _ leftBound rightBound, ?_⟩
    · simp only [Tree.blocks, Tree.length, codeLength, List.map_append, List.sum_append] at *
      omega
    · intro index within
      simp only [Tree.blocks, List.map_append]
      by_cases first : index < left.length
      · rw [getFromBlocks_append_left _ _ _ (by rw [decoded_length, ← leftLength]; exact first)]
        rw [Tree.payload, concat_low _ _ _ _ leftBound first]
        exact leftSound index first
      · have tail : index - left.length < right.length := by
          simp only [Tree.length] at within
          omega
        rw [getFromBlocks_append_right _ _ _ (by rw [decoded_length, ← leftLength]; omega)]
        rw [decoded_length, ← leftLength]
        have projected := concat_high left.payload right.payload left.length (index - left.length) leftBound
        rw [show left.length + (index - left.length) = index from by omega] at projected
        rw [Tree.payload, projected]
        exact rightSound _ tail

theorem getFromBlocks_complete (function : Nat → Nat) (start : Nat) (blocks : List Block)
    (agreement : ∀ index < (blocks.map Block.length).sum,
      getFromBlocks blocks index = some (function (start + index))) :
    checkBlocks function start blocks = true := by
  induction blocks generalizing start with
  | nil => rfl
  | cons block rest ih =>
    rw [checkBlocks_cons_iff]
    constructor
    · intro index
      have result := agreement index.val (by
        simp only [List.map_cons, List.sum_cons]
        omega)
      simpa only [getFromBlocks, if_pos index.isLt] using result
    · apply ih (start + block.length)
      intro index within
      have result := agreement (block.length + index) (by
        simp only [List.map_cons, List.sum_cons]
        omega)
      have outside : ¬block.length + index < block.length := by omega
      simpa only [getFromBlocks, if_neg outside, Nat.add_sub_cancel_left, Nat.add_assoc] using result

theorem Tree.checkBlocks_sound (function : Nat → Nat) (start : Nat) (data : Tree)
    (checked : data.check = true)
    (agreement : ∀ index < data.length, digit 65536 data.payload index = function (start + index)) :
    checkBlocks function start (data.blocks.map (Code.decode 65536)) = true := by
  obtain ⟨sameLength, _, source⟩ := data.check_sound checked
  apply getFromBlocks_complete
  intro index within
  have bounded : index < data.length := by rwa [decoded_length, ← sameLength] at within
  rw [source index bounded, agreement index bounded]

/-- Pack the complete reference span. Each word keeps its low 16 bits. -/
def referencePacked (function : Nat → Nat) (start count : Nat) : Nat :=
  Nat.ofDigits 65536 ((List.range count).map fun index => function (start + index) % 65536)

theorem referencePacked_bound (function : Nat → Nat) (start count : Nat) :
    referencePacked function start count < 65536 ^ count := by
  have result := Nat.ofDigits_lt_base_pow_length (b := 65536)
    (l := (List.range count).map fun index => function (start + index) % 65536)
    (by omega) (by
      intro value member
      obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
      exact Nat.mod_lt _ (by omega))
  simpa only [referencePacked, List.length_map, List.length_range] using result

theorem referencePacked_digit (function : Nat → Nat) (start count index : Nat)
    (within : index < count) :
    digit 65536 (referencePacked function start count) index = function (start + index) % 65536 := by
  have result := PackedRadix.extractDigitBase 65536
    ((List.range count).map fun index => function (start + index) % 65536) index (by omega)
    (by
      intro value member
      obtain ⟨position, _, rfl⟩ := List.mem_map.mp member
      exact Nat.mod_lt _ (by omega))
    (by simpa only [List.length_map, List.length_range] using within)
  simpa only [referencePacked, digit, List.getElem_map, List.getElem_range] using result

def Tree.checkReference (function : Nat → Nat) (start : Nat) : Tree → Bool
  | .leaf _ count payload => payload == referencePacked function start count
  | .branch left right => left.checkReference function start &&
      right.checkReference function (start + left.length)

theorem Tree.checkReference_sound (function : Nat → Nat) (start : Nat) (data : Tree)
    (checked : data.checkReference function start = true) :
    data.payload < 65536 ^ data.length ∧ ∀ index < data.length,
      digit 65536 data.payload index = function (start + index) % 65536 := by
  induction data generalizing start with
  | leaf blocks count payload =>
    simp only [Tree.checkReference, beq_iff_eq] at checked
    subst payload
    exact ⟨referencePacked_bound function start count, referencePacked_digit function start count⟩
  | branch left right leftIH rightIH =>
    simp only [Tree.checkReference, Bool.and_eq_true] at checked
    obtain ⟨leftBound, leftSound⟩ := leftIH start checked.1
    obtain ⟨rightBound, rightSound⟩ := rightIH (start + left.length) checked.2
    refine ⟨concat_bound _ _ _ _ leftBound rightBound, ?_⟩
    intro index within
    by_cases first : index < left.length
    · rw [Tree.payload, concat_low _ _ _ _ leftBound first]
      exact leftSound index first
    · have tail : index - left.length < right.length := by
        change index < left.length + right.length at within
        omega
      have projected := concat_high left.payload right.payload left.length (index - left.length) leftBound
      rw [show left.length + (index - left.length) = index from by omega] at projected
      rw [Tree.payload, projected, rightSound _ tail]
      congr 2
      omega

theorem Tree.referenceChecks_sound (function : Nat → Nat) (start : Nat) (data : Tree)
    (checked : data.check = true) (reference : data.checkReference function start = true)
    (bounded : ∀ index < data.length, function (start + index) < 65536) :
    checkBlocks function start (data.blocks.map (Code.decode 65536)) = true := by
  apply data.checkBlocks_sound function start checked
  intro index within
  have result := (data.checkReference_sound function start reference).2 index within
  simpa only [Nat.mod_eq_of_lt (bounded index within)] using result

/-- Check every bounded leaf with one proved numeric predicate. -/
def Tree.checkLeaves (check : Nat → Nat → Nat → Bool) (start : Nat) : Tree → Bool
  | .leaf _ count payload => check start count payload
  | .branch left right => left.checkLeaves check start && right.checkLeaves check (start + left.length)

theorem Tree.checkLeaves_sound (function : Nat → Nat) (check : Nat → Nat → Nat → Bool)
    (sound : ∀ start count payload, check start count payload = true →
      ∀ index < count, digit 65536 payload index = function (start + index))
    (start : Nat) (data : Tree) (checked : data.check = true)
    (reference : data.checkLeaves check start = true) :
    checkBlocks function start (data.blocks.map (Code.decode 65536)) = true := by
  induction data generalizing start with
  | leaf blocks count payload =>
    exact (Tree.leaf blocks count payload).checkBlocks_sound function start checked
      (sound start count payload reference)
  | branch left right leftIH rightIH =>
    simp only [Tree.check, Tree.checkLeaves, Bool.and_eq_true] at checked reference
    rw [Tree.blocks, List.map_append, checkBlocks_append_iff]
    constructor
    · exact leftIH start checked.1 reference.1
    · have sameLength := (left.check_sound checked.1).1
      rw [decoded_length, ← sameLength]
      exact rightIH (start + left.length) checked.2 reference.2

structure Request where
  start : Nat
  count : Nat
  payload : Nat

def Tree.requests (start : Nat) : Tree → List Request
  | .leaf _ count payload => [⟨start, count, payload⟩]
  | .branch left right => left.requests start ++ right.requests (start + left.length)

def checkRequests (check : Nat → Nat → Nat → Bool) (requests : List Request) : Bool :=
  requests.all fun request => check request.start request.count request.payload

theorem Tree.checkLeaves_requests (check : Nat → Nat → Nat → Bool) (start : Nat) (data : Tree) :
    data.checkLeaves check start = checkRequests check (data.requests start) := by
  induction data generalizing start with
  | leaf blocks count payload =>
    simp only [Tree.checkLeaves, Tree.requests, checkRequests, List.all_cons, List.all_nil, Bool.and_true]
  | branch left right leftIH rightIH =>
    simp only [Tree.checkLeaves, Tree.requests, checkRequests, List.all_append] at *
    rw [leftIH, rightIH]

end Airbender.Setup.Proofs.PackedWordColumn
