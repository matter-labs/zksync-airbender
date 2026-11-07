import Airbender.Review.Circuits.ReducedMachine.MemoryTokens
import Airbender.Proofs.ReducedMachine.NativeMainAuxiliary
import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic.FinCases

namespace Airbender.NativeMemoryTokenProofs
open NativeMemoryTokens Airbender.Blake2Worker.Native Airbender.ReducedMachine.NativeMainAuxiliary
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

private theorem vector_pair (value : Vector (ZMod mersenne31Modulus) 2) :
    #v[value[0],value[1]] = value := by
  apply Vector.ext
  intro i bound
  rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> rfl

theorem decode_encode (key : MemoryKey) : decodeKey (encodeKey key) = key := by
  rcases key with ⟨⟨indicator,low,high⟩,value,time⟩
  simp [decodeKey,encodeKey,encodeAddress,Nat.unpair_pair,vector_pair]

theorem encode_injective : Function.Injective encodeKey :=
  Function.LeftInverse.injective decode_encode

theorem address_injective : Function.Injective encodeAddress := by
  intro left right same
  have tokens : encodeKey ⟨left,#v[0,0],#v[0,0]⟩ = encodeKey ⟨right,#v[0,0],#v[0,0]⟩ := by
    simp only [encodeKey,same]
  exact congrArg MemoryKey.address (encode_injective tokens)

theorem equal_tokens (left right : MemoryKey) : encodeKey left = encodeKey right ↔ left = right :=
  encode_injective.eq_iff

/-- Pure permutation transport in both directions; no native matching premise is
    added and no scalar/challenge-product equality is used to obtain a permutation. -/
theorem permutation_encoding (left right : List MemoryKey) :
    (left.map encodeKey).Perm (right.map encodeKey) ↔ left.Perm right :=
  List.map_perm_map_iff encode_injective

theorem matching_encoding (initial terminal reads writes : List MemoryKey) :
    (initial.map encodeKey ++ writes.map encodeKey).Perm
      (terminal.map encodeKey ++ reads.map encodeKey) ↔
    (initial ++ writes).Perm (terminal ++ reads) := by
  simpa only [List.map_append] using permutation_encoding (initial++writes) (terminal++reads)

theorem mixed_address (w : Nat → ZMod mersenne31Modulus) (selector : Nat)
    (polarity : Bool) (columns : Vector Nat 2) :
    encodeAddress (nativeAddress w (.mixed selector polarity columns)) =
      Trace.MemoryAddress.code (.mixed selector polarity columns) w := by
  cases polarity <;> simp [encodeAddress,nativeAddress,Trace.MemoryAddress.code,Trace.pairCode]

theorem port_order : (List.finRange 3).map mainPort =
    Airbender.ReducedMachine.Native.importedConstraintsMemoryPorts.toList := by decide +kernel

theorem main_token (w : Nat → ZMod mersenne31Modulus) (slot : Fin 3) (write : Bool) :
    encodeKey (mainMemoryKey w slot write) =
      if write then Trace.writeToken Airbender.ReducedMachine.Native.importedConstraintsTraceColumns w (mainPort slot)
      else Trace.readToken w (mainPort slot) := by
  obtain ⟨p0,p1,p2⟩ := Airbender.ReducedMachine.NativeMainAuxiliaryProofs.port_geometry
  fin_cases slot <;> cases write
  all_goals simp [mainMemoryKey,p0,p1,p2,encodeKey,encodeAddress,nativeAddress,
    Trace.readToken,Trace.writeToken,Trace.rawPair,Trace.MemoryAddress.code,
    Trace.MemoryPort.readCode,Trace.MemoryPort.writeCode,Trace.WordColumns.code,
    Trace.WordColumns.evaluate,Trace.pairCode]

theorem main_list (w : Nat → ZMod mersenne31Modulus) (write : Bool) :
    ((List.finRange 3).map fun slot => encodeKey (mainMemoryKey w slot write)) = mainTokens w write := by
  unfold mainTokens
  rw [← port_order,List.map_map]
  apply List.map_congr_left
  intro slot _
  cases write <;> exact main_token w slot _

theorem worker_decoded (w : Nat → ZMod mersenne31Modulus) (slot : Fin 43) (write : Bool) :
    decodeKey (encodeKey (quotientMemoryKey w slot write)) = quotientMemoryKey w slot write :=
  decode_encode _

theorem worker_keys (w : Nat → ZMod mersenne31Modulus) (write : Bool) :
    (workerTokens w write).map decodeKey = (List.finRange 43).map (fun slot => quotientMemoryKey w slot write) := by
  simp only [workerTokens,List.map_map,Function.comp_def,decode_encode]

theorem worker_count (w : Nat → ZMod mersenne31Modulus) (write : Bool) :
    (workerTokens w write).length = 43 := by simp [workerTokens]

theorem argument_encoding {R : Type} [CommRing R] (embed : ZMod mersenne31Modulus →+* R)
    (ch : MemoryKeyChallenges R) (key : MemoryKey) :
    tokenArgument embed ch (encodeKey key) = memoryKeyArgument embed ch key := by
  simp only [tokenArgument,decode_encode]

theorem main_product {R : Type} [Field R] (embed : ZMod mersenne31Modulus →+* R)
    (ch : MemoryKeyChallenges R) (w : Nat → ZMod mersenne31Modulus) (write : Bool) :
    ((mainTokens w write).map (tokenArgument embed ch)).prod = mainMemoryProduct embed ch w write := by
  rw [← main_list,List.map_map]
  simp only [mainMemoryProduct,Function.comp_def,argument_encoding]

theorem worker_product {R : Type} [CommRing R] (embed : ZMod mersenne31Modulus →+* R)
    (ch : MemoryKeyChallenges R) (w : Nat → ZMod mersenne31Modulus) (write : Bool) :
    ((workerTokens w write).map (tokenArgument embed ch)).prod = memoryKeyProduct embed ch w write := by
  simp only [workerTokens,List.map_map,Function.comp_def,argument_encoding,memoryKeyProduct]

end Airbender.NativeMemoryTokenProofs
