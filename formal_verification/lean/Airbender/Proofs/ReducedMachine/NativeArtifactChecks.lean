import Airbender.Review.Circuits.ReducedMachine.NativeArtifact

namespace Airbender.ReducedMachine.NativeArtifactProofs
set_option warningAsError true
set_option Elab.async false
variable {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 4))

theorem equations : (FlatOperation.constraints (Native.importedConstraints setup)).length = 117 := rfl
theorem lookups : (FlatOperation.lookups (Native.importedConstraints setup)).length = 22 := rfl

theorem setup_rows : Native.importedConstraintsSetupColumns.genericRows = 5771521 := rfl

theorem argument_metadata : Native.importedConstraintsArgumentColumns =
    ⟨#v[126,127],#v[128,129],#v[130,131],#v[122,123],#v[124,125],92,94,93,3⟩ := rfl

theorem query0_fields :
    ((FlatOperation.lookups (Native.importedConstraints setup)).get ⟨16,by change 16 < 22; decide⟩).entry =
      #v[Expression.var ⟨36⟩, Expression.var ⟨56⟩, Expression.var ⟨57⟩, Expression.const (Int.cast (Int.ofNat 16))] := rfl

theorem query0_table :
    ((FlatOperation.lookups (Native.importedConstraints setup)).get ⟨16,by change 16 < 22; decide⟩).table =
      setup.toRaw := rfl

theorem query1_fields :
    ((FlatOperation.lookups (Native.importedConstraints setup)).get ⟨17,by change 17 < 22; decide⟩).entry =
      #v[Expression.var ⟨48⟩, Expression.var ⟨59⟩, Expression.var ⟨60⟩, Expression.const (Int.cast (Int.ofNat 16))] := rfl

theorem query1_table :
    ((FlatOperation.lookups (Native.importedConstraints setup)).get ⟨17,by change 17 < 22; decide⟩).table =
      setup.toRaw := rfl

theorem query2_fields :
    ((FlatOperation.lookups (Native.importedConstraints setup)).get ⟨18,by change 18 < 22; decide⟩).entry =
      #v[Expression.var ⟨100⟩, Expression.var ⟨101⟩, Expression.var ⟨102⟩, Expression.var ⟨103⟩] := rfl

theorem query2_table :
    ((FlatOperation.lookups (Native.importedConstraints setup)).get ⟨18,by change 18 < 22; decide⟩).table =
      setup.toRaw := rfl

theorem query3_fields :
    ((FlatOperation.lookups (Native.importedConstraints setup)).get ⟨19,by change 19 < 22; decide⟩).entry =
      #v[Expression.var ⟨104⟩, Expression.var ⟨105⟩, Expression.var ⟨106⟩, Expression.var ⟨107⟩] := rfl

theorem query3_table :
    ((FlatOperation.lookups (Native.importedConstraints setup)).get ⟨19,by change 19 < 22; decide⟩).table =
      setup.toRaw := rfl

theorem query4_fields :
    ((FlatOperation.lookups (Native.importedConstraints setup)).get ⟨20,by change 20 < 22; decide⟩).entry =
      #v[Expression.var ⟨108⟩, Expression.var ⟨109⟩, Expression.var ⟨110⟩, Expression.var ⟨111⟩] := rfl

theorem query4_table :
    ((FlatOperation.lookups (Native.importedConstraints setup)).get ⟨20,by change 20 < 22; decide⟩).table =
      setup.toRaw := rfl

theorem query5_fields :
    ((FlatOperation.lookups (Native.importedConstraints setup)).get ⟨21,by change 21 < 22; decide⟩).entry =
      #v[Expression.var ⟨112⟩, Expression.var ⟨113⟩, Expression.var ⟨114⟩, Expression.var ⟨115⟩] := rfl

theorem query5_table :
    ((FlatOperation.lookups (Native.importedConstraints setup)).get ⟨21,by change 21 < 22; decide⟩).table =
      setup.toRaw := rfl

end Airbender.ReducedMachine.NativeArtifactProofs
