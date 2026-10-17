import Airbender.Import.SetupEmbed
import Airbender.Review.Helpers.Tables.Range

namespace Airbender.Trace.NativeDecoder

/-- Independently imported real rows, the whole committed tail and native
    packing metadata. Public program binding and query authentication are
    separate from this data view. -/
structure PackedSetup where
  width : Nat
  realRows : Setup.TableData width
  padding : Setup.TableData width
  columnsMask : Array Bool
  tagged : Bool
  offset : Nat
  prefixTags : Setup.Column

/-- Restore omitted logical fields as zero; retain the actual discriminator in
    tagged setups. The extra constant for a separate decoder-only setup merely
    names that separate table. It does not change any physical setup column. -/
def PackedSetup.normalize (setup : PackedSetup) (packed : Vector Nat setup.width) : Vector Nat 10 :=
  Vector.ofFn fun column =>
    if column.val < 9 then
      if setup.columnsMask[column.val]?.getD false then
        packed.toArray[((setup.columnsMask.extract 0 column.val).filter id).size]?.getD 0
      else 0
    else if setup.tagged then packed.toArray[setup.width - 1]?.getD 0 else 46

def PackedSetup.row (setup : PackedSetup) (index : Fin (setup.realRows.length + setup.padding.length)) :
    Vector Nat 10 :=
  let data := if index.val < setup.realRows.length then setup.realRows else setup.padding
  let n := if index.val < setup.realRows.length then index.val else index.val - setup.realRows.length
  setup.normalize (data.columns.map fun column => (column.get? (data.offset + n)).getD 0)

/-- The complete actual decoder row domain, including unreachable unsupported
    rows and committed filler. Active queries must retain discriminator 46. -/
def PackedSetup.table {p : Nat} [Fact p.Prime] (setup : PackedSetup) :
    Table (ZMod p) (fields 10) := .fromStatic {
  name := "Airbender.ImportedDecoder"
  length := setup.realRows.length + setup.padding.length
  row i := (setup.row i).map (fun n : Nat => (Setup.signedValue n : ZMod p))
  index query := (query[0].val + 65536 * query[1].val) / 4
  Spec query := ∃ i : Fin (setup.realRows.length + setup.padding.length),
    query = (setup.row i).map (fun n : Nat => (Setup.signedValue n : ZMod p))
  contains_iff _ := Iff.rfl
}

/-- The normalized nine-field native query preserves the real tag check. -/
def activeQuery {p : Nat} (query : Vector (ZMod p) 9) : Vector (ZMod p) 10 :=
  Vector.ofFn fun column => if bound : column.val < 9 then query[column.val] else 46

/-- Logical native lookup over the complete physical domain. In the fixed
    leading, only the actual imported discriminator is needed: all other fields
    are deliberately unconstrained. The proof excludes that entire leading from
    decoder queries. Real decoder rows and committed padding retain every field.
    Authentication of these logical queries remains a separate boundary. -/
def PackedSetup.lookup {p : Nat} (setup : PackedSetup) (query : Vector (ZMod p) 9) : Prop :=
  ∃ index : Fin (setup.offset + setup.realRows.length + setup.padding.length),
    if leading : index.val < setup.offset then
      setup.tagged = true ∧ (46 : ZMod p) =
        (Setup.signedValue ((setup.prefixTags.get? index.val).getD 0) : ZMod p)
    else activeQuery query =
      (setup.row ⟨index.val - setup.offset, by have := index.isLt; omega⟩).map
        (fun n => (Setup.signedValue n : ZMod p))

end Airbender.Trace.NativeDecoder
