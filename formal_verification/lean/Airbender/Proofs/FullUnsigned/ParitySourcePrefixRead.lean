import Airbender.Proofs.FullUnsigned.ParityControlPrefixes
import Airbender.Proofs.FullUnsigned.ChiSourceController
import Airbender.Proofs.FullUnsigned.SourceColumnRanges

namespace Airbender.Setup.SourceCaptureParityProofs
open Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private noncomputable def sourceColumn (column : Fin 8) : Column :=
  (SourceCaptureParity.columns[column.val]?).getD ⟨#[]⟩
private noncomputable def binding (column : Fin 8) : SourceBank.ColumnBinding :=
  (SourceCaptureParity.columnBindings[column.val]'(by change column.val < 8; exact column.isLt)).1
private def prefixCount (column : Fin 8) : Nat :=
  match column.val with
  | 0 => 52
  | 1 => 16
  | 2 => 161
  | 3 => 58
  | 4 => 12
  | 5 => 10
  | 6 => 27
  | _ => 3

private noncomputable def sourceEntries (column : Fin 8) : List Nat :=
  match column.val with
  | 0 => SourceCaptureParity.entries_2904
  | 1 => SourceCaptureParity.entries_2932
  | 2 => SourceCaptureParity.entries_3100
  | 3 => SourceCaptureParity.entries_3177
  | 4 => SourceCaptureParity.entries_3206
  | 5 => SourceCaptureParity.entries_3282
  | 6 => SourceCaptureParity.entries_3289
  | _ => SourceCaptureParity.entries_3295

private noncomputable def prefixEntries (column : Fin 8) : List Nat :=
  match column.val with
  | 0 => ParityControlPrefix.Column0.entries
  | 1 => ParityControlPrefix.Column1.entries
  | 2 => ParityControlPrefix.Column2.entries
  | 3 => ParityControlPrefix.Column3.entries
  | 4 => ParityControlPrefix.Column4.entries
  | 5 => ParityControlPrefix.Column5.entries
  | 6 => ParityControlPrefix.Column6.entries
  | _ => ParityControlPrefix.Column7.entries

/-- Exact retained source blocks cover byte-iota, slots and control rows. -/
noncomputable def prefixBlocks (column : Fin 8) : List Block :=
  (prefixEntries column).map (binding column).blocks

private theorem source_column_binding (column : Fin 8) : sourceColumn column = (binding column).column := by
  fin_cases column <;> simp only [binding, SourceCaptureParity.columnBindings,
    List.getElem_cons_zero, List.getElem_cons_succ] <;> rfl
private theorem binding_entries (column : Fin 8) : (binding column).entries = sourceEntries column := by
  fin_cases column <;> simp only [binding, SourceCaptureParity.columnBindings,
    List.getElem_cons_zero, List.getElem_cons_succ, sourceEntries] <;> source_record_entries
private theorem source_prefix (column : Fin 8) :
    (sourceColumn column).blocks.toList.take (prefixCount column) = prefixBlocks column := by
  rw [source_column_binding]
  simp only [SourceBank.ColumnBinding.column, List.toList_toArray, ← List.map_take]
  unfold prefixBlocks
  apply congrArg (fun entries : List Nat => entries.map (binding column).blocks)
  rw [binding_entries]
  fin_cases column
  · simpa only [sourceEntries, prefixCount, prefixEntries] using ParityControlPrefix.Column0.matches
  · simpa only [sourceEntries, prefixCount, prefixEntries] using ParityControlPrefix.Column1.matches
  · simpa only [sourceEntries, prefixCount, prefixEntries] using ParityControlPrefix.Column2.matches
  · simpa only [sourceEntries, prefixCount, prefixEntries] using ParityControlPrefix.Column3.matches
  · simpa only [sourceEntries, prefixCount, prefixEntries] using ParityControlPrefix.Column4.matches
  · simpa only [sourceEntries, prefixCount, prefixEntries] using ParityControlPrefix.Column5.matches
  · simpa only [sourceEntries, prefixCount, prefixEntries] using ParityControlPrefix.Column6.matches
  · simpa only [sourceEntries, prefixCount, prefixEntries] using ParityControlPrefix.Column7.matches

private theorem prefix_covers : ∀ column : Fin 8, 65780 ≤ ((prefixBlocks column).map Block.length).sum := by
  decide +kernel

/-- Read the exact original source through its checked bounded prefix. -/
theorem source_prefix_get (column : Fin 8) (index : Fin 65780) :
    ((SourceCaptureParity.columns[column.val]?).getD ({ blocks := #[] } : Column)).get? index.val =
      getFromBlocks (prefixBlocks column) index.val := by
  change getFromBlocks (sourceColumn column).blocks.toList index.val = _
  have selected := getFromBlocks_take (sourceColumn column).blocks.toList (prefixCount column) index.val
    (by rw [source_prefix]; have covered := prefix_covers column; omega)
  rw [source_prefix] at selected
  exact selected

end Airbender.Setup.SourceCaptureParityProofs
