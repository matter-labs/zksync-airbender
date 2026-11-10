import Airbender.Proofs.Tables.PackedWordBounds

namespace Airbender.Setup.Proofs.PackedXor9Checks
open PackedSignedRun PackedWordBlocks
set_option warningAsError true
set_option maxRecDepth 32768

def indexPacked : Nat := 0x1ff01fe01fd01fc01fb01fa01f901f801f701f601f501f401f301f201f101f001ef01ee01ed01ec01eb01ea01e901e801e701e601e501e401e301e201e101e001df01de01dd01dc01db01da01d901d801d701d601d501d401d301d201d101d001cf01ce01cd01cc01cb01ca01c901c801c701c601c501c401c301c201c101c001bf01be01bd01bc01bb01ba01b901b801b701b601b501b401b301b201b101b001af01ae01ad01ac01ab01aa01a901a801a701a601a501a401a301a201a101a0019f019e019d019c019b019a0199019801970196019501940193019201910190018f018e018d018c018b018a0189018801870186018501840183018201810180017f017e017d017c017b017a0179017801770176017501740173017201710170016f016e016d016c016b016a0169016801670166016501640163016201610160015f015e015d015c015b015a0159015801570156015501540153015201510150014f014e014d014c014b014a0149014801470146014501440143014201410140013f013e013d013c013b013a0139013801370136013501340133013201310130012f012e012d012c012b012a0129012801270126012501240123012201210120011f011e011d011c011b011a0119011801170116011501140113011201110110010f010e010d010c010b010a010901080107010601050104010301020101010000ff00fe00fd00fc00fb00fa00f900f800f700f600f500f400f300f200f100f000ef00ee00ed00ec00eb00ea00e900e800e700e600e500e400e300e200e100e000df00de00dd00dc00db00da00d900d800d700d600d500d400d300d200d100d000cf00ce00cd00cc00cb00ca00c900c800c700c600c500c400c300c200c100c000bf00be00bd00bc00bb00ba00b900b800b700b600b500b400b300b200b100b000af00ae00ad00ac00ab00aa00a900a800a700a600a500a400a300a200a100a0009f009e009d009c009b009a0099009800970096009500940093009200910090008f008e008d008c008b008a0089008800870086008500840083008200810080007f007e007d007c007b007a0079007800770076007500740073007200710070006f006e006d006c006b006a0069006800670066006500640063006200610060005f005e005d005c005b005a0059005800570056005500540053005200510050004f004e004d004c004b004a0049004800470046004500440043004200410040003f003e003d003c003b003a0039003800370036003500340033003200310030002f002e002d002c002b002a0029002800270026002500240023002200210020001f001e001d001c001b001a0019001800170016001500140013001200110010000f000e000d000c000b000a0009000800070006000500040003000200010000
def repeatedOnes : Nat := 0x10001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001000100010001

theorem index_correct : indexPacked = Nat.ofDigits 65536 (List.range 512) := by decide +kernel
theorem ones_correct : repeatedOnes = Nat.ofDigits 65536 (List.replicate 512 1) := by decide +kernel

theorem extract_xor (left right index : Nat) :
    digit 65536 (left ^^^ right) index =
      digit 65536 left index ^^^ digit 65536 right index := by
  have power : (65536 : Nat) ^ index = 2 ^ (16 * index) := by
    rw [pow_mul]
    norm_num
  simp only [digit, power]
  rw [Nat.xor_div_two_pow]
  simpa only [show (2 : Nat) ^ 16 = 65536 by norm_num] using
    (Nat.xor_mod_two_pow (a := left / 2 ^ (16 * index))
      (b := right / 2 ^ (16 * index)) (n := 16))

def expectedRow (row : Nat) : Nat := (indexPacked ^^^ (row * repeatedOnes)) % 65536 ^ 512

theorem expected_digit (row column : Nat) (rowBound : row < 512) (columnBound : column < 512) :
    digit 65536 (expectedRow row) column = row ^^^ column := by
  have projected := segment_digit 65536 (indexPacked ^^^ (row * repeatedOnes)) 0 512 column columnBound
  simp only [pow_zero, Nat.div_one, Nat.zero_add] at projected
  rw [expectedRow, projected, extract_xor, index_correct, ones_correct]
  have indexDigit : digit 65536 (Nat.ofDigits 65536 (List.range 512)) column = column := by
    have extracted := PackedRadix.extractDigitBase 65536 (List.range 512) column (by omega)
      (fun value member => by have bound := List.mem_range.mp member; omega)
      (by simpa using columnBound)
    simpa only [digit, List.getElem_range] using extracted
  have repeated : digit 65536 (row * Nat.ofDigits 65536 (List.replicate 512 1)) column = row := by
    rw [Nat.mul_ofDigits]
    simp only [List.map_replicate, mul_one]
    have extracted := PackedRadix.extractDigitBase 65536 (List.replicate 512 row) column (by omega)
      (fun value member => by have same := List.eq_of_mem_replicate member; omega)
      (by simpa using columnBound)
    simpa only [digit, List.getElem_replicate] using extracted
  rw [indexDigit, repeated, Nat.xor_comm]

def window (row : Nat) : Nat := expectedRow row + 65536 ^ 512 * expectedRow (row + 1)
def span (origin length : Nat) : Nat := (window (origin / 512) / 65536 ^ (origin % 512)) % 65536 ^ length
def legal (origin length : Nat) : Bool := origin + length ≤ 262144 && origin % 512 + length ≤ 1024

theorem window_low (row index : Nat) (rowBound : row < 512) (within : index < 512) :
    digit 65536 (window row) index = row ^^^ index := by
  have bounded : expectedRow row < 65536 ^ 512 := Nat.mod_lt _ (by positivity)
  have reduced : window row % 65536 ^ 512 = expectedRow row := by
    simp only [window, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt bounded]
  have projected := segment_digit 65536 (window row) 0 512 index within
  simp only [Nat.pow_zero, Nat.div_one, Nat.zero_add, reduced] at projected
  rw [← projected]
  exact expected_digit row index rowBound within

theorem window_high (row index : Nat) (rowBound : row + 1 < 512) (within : index < 512) :
    digit 65536 (window row) (512 + index) = (row + 1) ^^^ index := by
  have bounded : expectedRow row < 65536 ^ 512 := Nat.mod_lt _ (by positivity)
  have divided : window row / 65536 ^ 512 = expectedRow (row + 1) := by
    simp only [window, Nat.add_mul_div_left _ _ (show 0 < 65536 ^ 512 by positivity),
      Nat.div_eq_of_lt bounded, Nat.zero_add]
  unfold digit
  rw [pow_add, ← Nat.div_div_eq_div_mul, divided]
  exact expected_digit (row + 1) index rowBound within

theorem span_digit (origin length index : Nat) (accepted : legal origin length = true)
    (within : index < length) :
    digit 65536 (span origin length) index = (origin + index) / 512 ^^^ (origin + index) % 512 := by
  simp only [legal, Bool.and_eq_true, decide_eq_true_eq] at accepted
  have originParts := Nat.div_add_mod origin 512
  have totalParts := Nat.div_add_mod (origin + index) 512
  have projected := segment_digit 65536 (window (origin / 512)) (origin % 512) length index within
  rw [span, projected]
  by_cases first : origin % 512 + index < 512
  · rw [window_low (origin / 512) (origin % 512 + index) (by omega) first]
    exact congrArg₂ Nat.xor (by omega) (by omega)
  · have columnBound : origin % 512 + index - 512 < 512 := by omega
    have indexSplit : origin % 512 + index = 512 + (origin % 512 + index - 512) := by omega
    rw [indexSplit, window_high (origin / 512) _ (by omega) columnBound]
    exact congrArg₂ Nat.xor (by omega) (by omega)

def checkBlock (origin : Nat) (block : Code) : Bool :=
  legal origin block.length && PackedWordBounds.fastValid block.input &&
    block.input.packed 65536 == span origin block.length

def check (origin : Nat) (blocks : List Code) : Bool :=
  (List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun block _ tail position =>
      match position with
      | 0 => checkBlock 0 block && tail block.length
      | next + 1 => checkBlock (next + 1) block && tail (next + 1 + block.length)) blocks) origin

theorem check_cons (origin : Nat) (block : Code) (rest : List Code) :
    check origin (block :: rest) = (checkBlock origin block && check (origin + block.length) rest) := by
  cases origin with
  | zero => simp only [check, Nat.zero_add]
  | succ origin => rfl

theorem checkBlock_sound (origin : Nat) (block : Code) (checked : checkBlock origin block = true)
    (index : Nat) (within : index < (block.decode 65536).length) :
    (block.decode 65536).get? index = some ((origin + index) / 512 ^^^ (origin + index) % 512) := by
  simp only [checkBlock, Bool.and_eq_true, beq_iff_eq] at checked
  have raw := input_sound 65536 (by omega) block (PackedWordBounds.fastValid_sound block.input checked.1.2) index (by rwa [decode_length] at within)
  rw [checked.2, span_digit origin block.length index checked.1.1 (by rwa [decode_length] at within)] at raw
  exact raw

theorem check_sound (origin : Nat) (blocks : List Code) (checked : check origin blocks = true) :
    checkBlocks (fun index => index / 512 ^^^ index % 512) origin (blocks.map (Code.decode 65536)) = true := by
  induction blocks generalizing origin with
  | nil => rfl
  | cons block rest ih =>
    simp only [check_cons, Bool.and_eq_true] at checked
    rw [List.map_cons, checkBlocks_cons_iff]
    constructor
    · intro index
      exact checkBlock_sound origin block checked.1 index.val index.isLt
    · rw [decode_length]
      exact ih _ checked.2

structure Request where
  origin : Nat
  blocks : List Code
  length : Nat

def checkRequests (requests : List Request) : Bool :=
  requests.all (fun request => check request.origin request.blocks &&
    (request.blocks.map Code.length).sum == request.length)

theorem requests_sound (requests : List Request) (checked : checkRequests requests = true)
    (index : Nat) (request : Request) (found : requests[index]? = some request) :
    checkBlocks (fun value => value / 512 ^^^ value % 512) request.origin
      (request.blocks.map (Code.decode 65536)) = true ∧
    ((request.blocks.map (Code.decode 65536)).map Block.length).sum = request.length := by
  obtain ⟨within, same⟩ := List.getElem?_eq_some_iff.mp found
  have member : request ∈ requests := same ▸ List.getElem_mem within
  have result := List.all_eq_true.mp checked request member
  simp only [Bool.and_eq_true, beq_iff_eq] at result
  refine ⟨check_sound request.origin request.blocks result.1, ?_⟩
  simpa only [List.map_map, Function.comp_def, decode_length] using result.2

end Airbender.Setup.Proofs.PackedXor9Checks
