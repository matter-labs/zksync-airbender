#!/usr/bin/env python3
"""Refine the whole unified native non-decoder table including committed padding."""
import argparse
from export_gkr_translations import LEAN
from gkr_unified_prefix import plans


def content():
    out='import GKRProtocol.ROMNative.UnifiedRows\nimport GKRProtocol.ROMNative.UnifiedTag\n\nnamespace Airbender.Compiler.ROMNative.UnifiedBoundary\nopen Airbender Airbender.Compiler Airbender.Setup\nset_option warningAsError true\nset_option Elab.async false\nset_option maxRecDepth 65536\nset_option maxHeartbeats 8000000\n\nabbrev nativeSetup := UnifiedRows.nativeSetup\n\n'
    for col in range(10):
        artifact,blocks,positions,stop,groups,regions=plans(col)
        owner=f'UnifiedPrefixNative.Column{col}' if col==1 else f'UnifiedAllPrefix.Column{col}'
        orig=f'{owner}.original' if col==1 else f'{owner}.originals.flatten'
        tail=f'{owner}.suffix'
        full=f'Data.GKRSetup.Unified.setupColumn{col}';last=len(blocks)-1
        out+=f'column_blocks_part paddingFront{col} from {full} start {stop} stop {last}\n\n'
        out+=f'theorem paddingShape{col} : {tail} = paddingFront{col} ++ [Block.affine 5242495 0 0] := by rfl\n\n'
        out+=f'theorem paddingFrontLength{col} : (paddingFront{col}.map Block.length).sum = {3146113-positions[stop]} := by decide +kernel\n\n'
        out+=f'theorem paddingValue{col} (row : Fin 8388608) (lower : 3146113 ≤ row.val) : {full}.get? row.val = some 0 := by\n'
        out+=f'  change Setup.getFromBlocks {full}.blocks.toList row.val = _\n  rw [{owner}.sourceShape, getFromBlocks_append, {owner}.originalLength, if_neg (by omega), paddingShape{col}, getFromBlocks_append, paddingFrontLength{col}, if_neg (by omega)]\n'
        out+='  rw [Setup.getFromBlocks, if_pos (by have := row.isLt; change row.val - '+str(positions[stop])+' - '+str(3146113-positions[stop])+' < 5242495; omega)]\n'
        out+='  exact constant_block_get _ _ _ (by have := row.isLt; omega)\n\n'
    out+='theorem decoder_tag (row : Fin nativeSetup.imported.data.length)\n    (lower : 2097537 ≤ row.val) (upper : row.val < 3146113) : nativeSetup.value row (.generic 9) = 46 := by\n'
    out+='  rw [UnifiedTag.tag_value, if_neg (by omega)]\n'
    # Constant tag rows before the decoder are deliberately traversed with one branch at a time.
    regions=plans(9)[0]['tables'];remaining='(row.val - 1)'
    for region in regions[1:]:
        size=region['length'];tag=region['id']
        out+=f'  change (if {remaining} < {size} then _ else _) = 46\n  rw [if_neg (by omega)]\n'
        remaining=f'({remaining} - {size})'
    out+=f'  change (if {remaining} < 1048576 then _ else _) = 46\n  rw [if_pos (by omega)]\n  norm_num\n\n'
    out+='theorem padding_row (row : Fin 8388608) (lower : 3146113 ≤ row.val) :\n    UnifiedRows.nativeRow row = Vector.replicate 10 0 := by\n  apply Vector.ext\n  intro column bound\n  simp only [UnifiedRows.nativeRow, TableData.row, Vector.getElem_map, Vector.getElem_replicate,\n    show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]\n  interval_cases column\n'
    for col in range(10):out+=f'  · change ((Setup.signedValue ((Data.GKRSetup.Unified.setupColumn{col}.get? row.val).getD 0)) : Source.BaseField) = 0\n    rw [paddingValue{col} row lower]\n    rfl\n'
    out+='\ntheorem full_table_refinement {query : Vector Source.BaseField 10}\n    (member : (nativeSetup.imported.data.table "Airbender.Native.UnifiedReduced").Contains #[] query)\n    (notDecoder : query[9] ≠ 46) : (UnifiedReduced.Setup.importedTable (p := babyBearModulus)).Contains #[] query := by\n'
    out+='  obtain ⟨row, equal⟩ := member\n  change query = UnifiedRows.nativeRow row at equal\n  by_cases beforeDecoder : row.val < 2097537\n  · have retained := UnifiedRows.prefix_member ⟨row.val, beforeDecoder⟩\n    change (UnifiedReduced.Setup.importedTable (p := babyBearModulus)).Contains #[] (UnifiedRows.nativeRow row) at retained\n    exact equal.symm ▸ retained\n'
    out+='  · have lower : 3146113 ≤ row.val := by\n      by_contra earlier\n      have tag := decoder_tag row (by omega) (by omega)\n      apply notDecoder\n      rw [equal]\n      rw [nativeSetup.value_generic row (⟨9, by decide⟩ : Fin 10)] at tag\n      simpa only [UnifiedRows.nativeRow, Vector.getElem_map] using tag\n'
    out+='    rw [padding_row row lower] at equal\n    refine ⟨⟨0, by decide⟩, equal.trans ?_⟩\n    decide +kernel\n\nend Airbender.Compiler.ROMNative.UnifiedBoundary\n'
    return out


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for flag in ['write','check']:parser.add_argument('--'+flag,action='store_true')
    args=parser.parse_args();path=LEAN/'GKRProtocol/ROMNative/UnifiedBoundary.lean';text=content()
    if args.check and (not path.exists() or path.read_text()!=text):raise ValueError('unified boundary scaffold changed')
    if args.write and (not path.exists() or path.read_text()!=text):path.write_text(text)
    print('GKRProtocol.ROMNative.UnifiedBoundary')

if __name__=='__main__':main()
