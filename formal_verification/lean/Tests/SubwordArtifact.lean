import Airbender.Review.Circuits.SubwordMemory.Lookups
import Airbender.Proofs.SubwordMemory.NativeLookup
import Airbender.Proofs.Tables.AlignedWordROM

namespace Tests.SubwordArtifact
open Airbender Verification
set_option autoImplicit false

/-- error: v2 fixed lookups require an explicit native target -/
#guard_msgs in
import_clean noProfile from "../../cs/subword_only_load_store_preprocessed_layout.json"

/-- error: native fixed tables do not match the explicit target -/
#guard_msgs in
import_clean wrongProfile from "../../cs/subword_only_load_store_preprocessed_layout.json" word_memory_lookups

/-- error: native fixed tables do not match the explicit target -/
#guard_msgs in
import_clean crossedShift from "../../cs/subword_only_load_store_preprocessed_layout.json" shift_binop_lookups

/-- error: choose one native fixed-table profile -/
#guard_msgs in
import_clean crossedProfile from "../../cs/subword_only_load_store_preprocessed_layout.json" word_memory_lookups subword_memory_lookups

/-- error: native fixed tables do not match the explicit target -/
#guard_msgs in
import_clean crossedWord from "../../cs/word_only_load_store_preprocessed_layout.json" subword_memory_lookups

theorem equation_count (rom : WordROM) :
    (FlatOperation.constraints (SubwordMemory.importedConstraints (p := mersenne31Modulus) rom)).length = 51 := rfl

theorem lookup_count (rom : WordROM) :
    (FlatOperation.lookups (SubwordMemory.importedConstraints (p := mersenne31Modulus) rom)).length = 14 := rfl

theorem query0_retains_selector (rom : WordROM) :
    ((FlatOperation.lookups (SubwordMemory.importedConstraints (p := mersenne31Modulus) rom)).get
      ⟨12, by change 12 < 14; decide⟩).entry =
      #v[Expression.var ⟨52⟩,Expression.var ⟨53⟩,Expression.var ⟨54⟩,Expression.var ⟨55⟩] := rfl

theorem query1_retains_selector (rom : WordROM) :
    ((FlatOperation.lookups (SubwordMemory.importedConstraints (p := mersenne31Modulus) rom)).get
      ⟨13, by change 13 < 14; decide⟩).entry =
      #v[Expression.var ⟨56⟩,Expression.var ⟨57⟩,Expression.var ⟨58⟩,Expression.var ⟨59⟩] := rfl

theorem selector_is_evaluated (rom : WordROM) (env : Environment (ZMod mersenne31Modulus)) :
    ((NativeSubwordLookup.lookup rom
      #v[Expression.var ⟨52⟩,Expression.var ⟨53⟩,Expression.var ⟨54⟩]
      (Expression.var ⟨55⟩)).entry[3]'(by change 3 < 4; decide)).eval env = env.get 55 := rfl

theorem native_tagged_width (rom : WordROM) :
    (NativeSubwordLookup.table (p := mersenne31Modulus) rom).toRaw.arity = 4 := rfl

theorem native_fixed_placements :
    [(NativeSubwordOffset.data.nativeOffset,NativeSubwordOffset.data.length),
     (NativeSubwordLoad.data.nativeOffset,NativeSubwordLoad.data.length),
     (NativeSubwordStoreClear.data.nativeOffset,NativeSubwordStoreClear.data.length),
     (NativeSubwordStorePlace.data.nativeOffset,NativeSubwordStorePlace.data.length)] =
    [(65537,2097152),(2162689,2097152),(5308417,2097152),(7405569,2097152)] := rfl

def rom : WordROM := ⟨[BitVec.ofNat 32 4294934656,BitVec.ofNat 32 2147418113],by decide⟩

theorem aligned_key_is_word_index : rom.alignedRow ⟨1,by decide⟩ = #v[1,1,32767] := by decide +kernel

theorem ordinary_key_is_byte_address : rom.row ⟨1,by decide⟩ = #v[4,1,32767] := by decide +kernel

theorem aligned_padding : rom.alignedRow ⟨1048575,by decide⟩ = #v[1048575,4211,49152] := by decide +kernel

theorem aligned_query_member : (romAlignedWordTable (p := mersenne31Modulus) rom).Contains #[]
    #v[1,1,32767] := by
  refine ⟨⟨1,by decide⟩,?_⟩
  decide +kernel

theorem aligned_wrong_byte_key_rejected : ¬ (romAlignedWordTable (p := mersenne31Modulus) rom).Contains #[]
    #v[4,1,32767] := by
  intro member
  have values := AlignedWordROMProofs.values (by decide : 1048576 < mersenne31Modulus) member
  have literal : (((rom.word (4 : ZMod mersenne31Modulus).val).toNat % 65536 : Nat) :
    ZMod mersenne31Modulus) = 4211 := by decide +kernel
  have bad := values.2.1.trans literal
  exact (by decide +kernel : (1 : ZMod mersenne31Modulus) ≠ 4211) bad

theorem aligned_changed_output_rejected : ¬ (romAlignedWordTable (p := mersenne31Modulus) rom).Contains #[]
    #v[1,2,32767] := by
  intro member
  have values := AlignedWordROMProofs.values (by decide : 1048576 < mersenne31Modulus) member
  have literal : (((rom.word (1 : ZMod mersenne31Modulus).val).toNat % 65536 : Nat) :
    ZMod mersenne31Modulus) = 1 := by decide +kernel
  have bad := values.2.1.trans literal
  exact (by decide +kernel : (2 : ZMod mersenne31Modulus) ≠ 1) bad

end Tests.SubwordArtifact
