import Airbender.Review.Circuits.ReducedMachine.Artifact

namespace Airbender.ReducedMachine.Proofs
set_option warningAsError true
set_option Elab.async false
variable {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 4))

theorem equation_count : (FlatOperation.constraints (importedConstraints setup)).length = 119 := rfl

theorem lookup_count : (FlatOperation.lookups (importedConstraints setup)).length = 22 := rfl

theorem argument_metadata : importedConstraintsArgumentColumns =
    ⟨#v[125,126], #v[127,128], #v[129,130], #v[121,122], #v[123,124], 91,93,92,3⟩ := rfl

theorem query0_fields :
    ((FlatOperation.lookups (importedConstraints setup)).get ⟨16, by change 16 < 22; decide⟩).entry =
      #v[Expression.var ⟨36⟩, Expression.var ⟨56⟩, Expression.var ⟨57⟩, Expression.const (Int.cast (Int.ofNat 16))] := rfl

theorem query0_table :
    ((FlatOperation.lookups (importedConstraints setup)).get ⟨16, by change 16 < 22; decide⟩).table =
      setup.toRaw := rfl

theorem query1_fields :
    ((FlatOperation.lookups (importedConstraints setup)).get ⟨17, by change 17 < 22; decide⟩).entry =
      #v[Expression.var ⟨48⟩, Expression.var ⟨59⟩, Expression.var ⟨60⟩, Expression.const (Int.cast (Int.ofNat 16))] := rfl

theorem query1_table :
    ((FlatOperation.lookups (importedConstraints setup)).get ⟨17, by change 17 < 22; decide⟩).table =
      setup.toRaw := rfl

theorem query2_fields :
    ((FlatOperation.lookups (importedConstraints setup)).get ⟨18, by change 18 < 22; decide⟩).entry =
      #v[Expression.var ⟨99⟩, Expression.var ⟨100⟩, Expression.var ⟨101⟩, Expression.var ⟨102⟩] := rfl

theorem query2_table :
    ((FlatOperation.lookups (importedConstraints setup)).get ⟨18, by change 18 < 22; decide⟩).table =
      setup.toRaw := rfl

theorem query3_fields :
    ((FlatOperation.lookups (importedConstraints setup)).get ⟨19, by change 19 < 22; decide⟩).entry =
      #v[Expression.var ⟨103⟩, Expression.var ⟨104⟩, Expression.var ⟨105⟩, Expression.var ⟨106⟩] := rfl

theorem query3_table :
    ((FlatOperation.lookups (importedConstraints setup)).get ⟨19, by change 19 < 22; decide⟩).table =
      setup.toRaw := rfl

theorem query4_fields :
    ((FlatOperation.lookups (importedConstraints setup)).get ⟨20, by change 20 < 22; decide⟩).entry =
      #v[Expression.var ⟨107⟩, Expression.var ⟨108⟩, Expression.var ⟨109⟩, Expression.var ⟨110⟩] := rfl

theorem query4_table :
    ((FlatOperation.lookups (importedConstraints setup)).get ⟨20, by change 20 < 22; decide⟩).table =
      setup.toRaw := rfl

theorem query5_fields :
    ((FlatOperation.lookups (importedConstraints setup)).get ⟨21, by change 21 < 22; decide⟩).entry =
      #v[Expression.var ⟨111⟩, Expression.var ⟨112⟩, Expression.var ⟨113⟩, Expression.var ⟨114⟩] := rfl

theorem query5_table :
    ((FlatOperation.lookups (importedConstraints setup)).get ⟨21, by change 21 < 22; decide⟩).table =
      setup.toRaw := rfl

end Airbender.ReducedMachine.Proofs
