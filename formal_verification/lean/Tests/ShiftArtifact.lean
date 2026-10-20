import Airbender.Review.Circuits.ShiftBinop.Artifact
import Airbender.Review.Helpers.Properties
import Airbender.Proofs.Mersenne31
import Airbender.Proofs.ShiftBinop.NativeLookup

namespace Tests.ShiftArtifact
open Airbender Verification

/-- error: v2 fixed lookups require an explicit native target -/
#guard_msgs in
import_clean noProfile from "../../cs/shift_binop_csrrw_preprocessed_layout.json"

/-- error: native fixed tables do not match the explicit target -/
#guard_msgs in
import_clean wrongProfile from "../../cs/shift_binop_csrrw_preprocessed_layout.json" mul_div_lookups

/-- error: choose one native fixed-table profile -/
#guard_msgs in
import_clean crossedProfile from "../../cs/shift_binop_csrrw_preprocessed_layout.json" mul_div_lookups shift_binop_lookups

theorem equation_count :
    (FlatOperation.constraints (ShiftBinop.importedConstraints (p := mersenne31Modulus))).length = 50 := rfl

theorem lookup_count :
    (FlatOperation.lookups (ShiftBinop.importedConstraints (p := mersenne31Modulus))).length = 12 := rfl

theorem setup_geometry : ShiftBinop.importedConstraintsSetupColumns =
    ⟨16777216,16,0,1,2,1,6,1048576,10817537⟩ := rfl

theorem native_trace_metadata : ShiftBinop.importedConstraintsTraceColumns =
    ⟨4,#v[0,1],#v[13,14],#v[2,3],#v[15,16],
      #[⟨0,#v[65,66],67⟩,⟨1,#v[68,69],70⟩,⟨2,#v[71,72],73⟩]⟩ := rfl

theorem memory_metadata : ShiftBinop.importedConstraintsMemoryPorts =
    #[⟨⟨0,#v[65,66],67⟩,.register 5,.u16 #v[23,24],none⟩,
      ⟨⟨1,#v[68,69],70⟩,.register 6,.u16 #v[25,26],none⟩,
      ⟨⟨2,#v[71,72],73⟩,.register 7,.u16 #v[57,58],some (.u16 #v[59,60])⟩] := rfl

theorem decoder_metadata : ShiftBinop.importedConstraintsDecoderColumns =
    ⟨5,6,7,8,#v[9,10],11,12⟩ := rfl

theorem query0_retains_selector :
    ((FlatOperation.lookups (ShiftBinop.importedConstraints (p := mersenne31Modulus))).get
      ⟨8, by decide⟩).entry =
      #v[Expression.var ⟨39⟩, Expression.var ⟨40⟩, Expression.var ⟨41⟩, Expression.var ⟨42⟩] := rfl

theorem query1_retains_selector :
    ((FlatOperation.lookups (ShiftBinop.importedConstraints (p := mersenne31Modulus))).get
      ⟨9, by decide⟩).entry =
      #v[Expression.var ⟨43⟩, Expression.var ⟨44⟩, Expression.var ⟨45⟩, Expression.var ⟨46⟩] := rfl

theorem query2_retains_selector :
    ((FlatOperation.lookups (ShiftBinop.importedConstraints (p := mersenne31Modulus))).get
      ⟨10, by decide⟩).entry =
      #v[Expression.var ⟨47⟩, Expression.var ⟨48⟩, Expression.var ⟨49⟩, Expression.var ⟨50⟩] := rfl

theorem query3_retains_selector :
    ((FlatOperation.lookups (ShiftBinop.importedConstraints (p := mersenne31Modulus))).get
      ⟨11, by decide⟩).entry =
      #v[Expression.var ⟨51⟩, Expression.var ⟨52⟩, Expression.var ⟨53⟩, Expression.var ⟨54⟩] := rfl

theorem selector_is_evaluated (env : Environment (ZMod mersenne31Modulus)) :
    (NativeShiftLookup.lookup #v[Expression.var ⟨39⟩, Expression.var ⟨40⟩, Expression.var ⟨41⟩]
      (Expression.var ⟨42⟩)).entry[3].eval env = env.get 42 := rfl

theorem native_placements :
  [(NativeBinary.dataZero.nativeOffset, NativeBinary.dataZero.length), (NativeBinary.dataXor.nativeOffset, NativeBinary.dataXor.length), (NativeBinary.dataOr.nativeOffset, NativeBinary.dataOr.length), (NativeBinary.dataAnd.nativeOffset, NativeBinary.dataAnd.length), (NativeShiftCsr.data.nativeOffset, NativeShiftCsr.data.length), (NativeShiftScalars.dataTruncate.nativeOffset, NativeShiftScalars.dataTruncate.length), (NativeSllLow.data.nativeOffset, NativeSllLow.data.length), (NativeSllHigh.data.nativeOffset, NativeSllHigh.data.length), (NativeSrlLow.data.nativeOffset, NativeSrlLow.data.length), (NativeSrlHigh.data.nativeOffset, NativeSrlHigh.data.length), (NativeShiftScalars.dataSignFill.nativeOffset, NativeShiftScalars.dataSignFill.length), (NativeShiftScalars.dataRange.nativeOffset, NativeShiftScalars.dataRange.length)] =
  [(0, 1), (1, 65536), (65537, 65536), (131073, 65536), (196609, 4096), (200705, 65536), (266241, 2097152), (2363393, 2097152), (4460545, 2097152), (6557697, 2097152), (8654849, 2097152), (10752001, 65536)] := rfl

theorem actual_zero_member : (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[0,0,0,0] := by
  refine ⟨⟨0, by decide⟩, ?_⟩
  decide +kernel

theorem actual_nondeterminism_csr_member : (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[1984,1,0,25] := by
  refine ⟨⟨198593, by decide⟩, ?_⟩
  decide +kernel

theorem actual_final_row_member : (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] #v[65535,0,0,53] := by
  refine ⟨⟨10817536, by decide⟩, ?_⟩
  decide +kernel

end Tests.ShiftArtifact
