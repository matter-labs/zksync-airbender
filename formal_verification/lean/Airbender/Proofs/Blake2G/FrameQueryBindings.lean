import Airbender.Proofs.Blake2G.FrameQueryEntries
import Airbender.Proofs.Blake2G.Fragment

namespace Airbender.Blake2G.Proofs.FrameQueryShapes
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem lookup0_eq_mk {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 9)) :
    ((FlatOperation.lookups (mixingConstraints table)).get
      ⟨0, by rw [mixing_lookup_count]; decide⟩) = Lookup.mk table.toRaw (entry0 table) := rfl

theorem lookup1_eq_mk {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 9)) :
    ((FlatOperation.lookups (mixingConstraints table)).get
      ⟨1, by rw [mixing_lookup_count]; decide⟩) = Lookup.mk table.toRaw (entry1 table) := rfl

theorem lookup2_eq_mk {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 9)) :
    ((FlatOperation.lookups (mixingConstraints table)).get
      ⟨2, by rw [mixing_lookup_count]; decide⟩) = Lookup.mk table.toRaw (entry2 table) := rfl

theorem lookup3_eq_mk {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 9)) :
    ((FlatOperation.lookups (mixingConstraints table)).get
      ⟨3, by rw [mixing_lookup_count]; decide⟩) = Lookup.mk table.toRaw (entry3 table) := rfl

theorem lookup4_eq_mk {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 9)) :
    ((FlatOperation.lookups (mixingConstraints table)).get
      ⟨4, by rw [mixing_lookup_count]; decide⟩) = Lookup.mk table.toRaw (entry4 table) := rfl

theorem lookup5_eq_mk {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 9)) :
    ((FlatOperation.lookups (mixingConstraints table)).get
      ⟨5, by rw [mixing_lookup_count]; decide⟩) = Lookup.mk table.toRaw (entry5 table) := rfl

theorem lookup6_eq_mk {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 9)) :
    ((FlatOperation.lookups (mixingConstraints table)).get
      ⟨6, by rw [mixing_lookup_count]; decide⟩) = Lookup.mk table.toRaw (entry6 table) := rfl

theorem lookup7_eq_mk {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 9)) :
    ((FlatOperation.lookups (mixingConstraints table)).get
      ⟨7, by rw [mixing_lookup_count]; decide⟩) = Lookup.mk table.toRaw (entry7 table) := rfl

theorem lookup8_eq_mk {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 9)) :
    ((FlatOperation.lookups (mixingConstraints table)).get
      ⟨8, by rw [mixing_lookup_count]; decide⟩) = Lookup.mk table.toRaw (entry8 table) := rfl

theorem lookup9_eq_mk {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 9)) :
    ((FlatOperation.lookups (mixingConstraints table)).get
      ⟨9, by rw [mixing_lookup_count]; decide⟩) = Lookup.mk table.toRaw (entry9 table) := rfl

theorem lookup10_eq_mk {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 9)) :
    ((FlatOperation.lookups (mixingConstraints table)).get
      ⟨10, by rw [mixing_lookup_count]; decide⟩) = Lookup.mk table.toRaw (entry10 table) := rfl

theorem lookup11_eq_mk {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 9)) :
    ((FlatOperation.lookups (mixingConstraints table)).get
      ⟨11, by rw [mixing_lookup_count]; decide⟩) = Lookup.mk table.toRaw (entry11 table) := rfl

theorem lookup12_eq_mk {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 9)) :
    ((FlatOperation.lookups (mixingConstraints table)).get
      ⟨12, by rw [mixing_lookup_count]; decide⟩) = Lookup.mk table.toRaw (entry12 table) := rfl

theorem lookup13_eq_mk {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 9)) :
    ((FlatOperation.lookups (mixingConstraints table)).get
      ⟨13, by rw [mixing_lookup_count]; decide⟩) = Lookup.mk table.toRaw (entry13 table) := rfl

theorem lookup14_eq_mk {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 9)) :
    ((FlatOperation.lookups (mixingConstraints table)).get
      ⟨14, by rw [mixing_lookup_count]; decide⟩) = Lookup.mk table.toRaw (entry14 table) := rfl

theorem lookup15_eq_mk {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 9)) :
    ((FlatOperation.lookups (mixingConstraints table)).get
      ⟨15, by rw [mixing_lookup_count]; decide⟩) = Lookup.mk table.toRaw (entry15 table) := rfl

theorem lookup16_eq_mk {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 9)) :
    ((FlatOperation.lookups (mixingConstraints table)).get
      ⟨16, by rw [mixing_lookup_count]; decide⟩) = Lookup.mk table.toRaw (entry16 table) := rfl

theorem lookup17_eq_mk {p : Nat} [Fact p.Prime] (table : Table (ZMod p) (fields 9)) :
    ((FlatOperation.lookups (mixingConstraints table)).get
      ⟨17, by rw [mixing_lookup_count]; decide⟩) = Lookup.mk table.toRaw (entry17 table) := rfl

end Airbender.Blake2G.Proofs.FrameQueryShapes
