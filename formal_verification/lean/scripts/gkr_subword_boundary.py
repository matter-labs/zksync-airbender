#!/usr/bin/env python3
"""Refine non-decoder full native subword membership, including committed padding."""
import argparse
import json
from export_gkr_translations import LEAN


def content():
    artifact=json.loads((LEAN/'artifacts/setup/subword-memory.json').read_text())
    out='import Airbender.Proofs.GKRProtocol.ROMNative.SubwordRows\n\nnamespace Airbender.Compiler.ROMNative.SubwordBoundary\nopen Airbender Airbender.Compiler Airbender.Setup\nset_option warningAsError true\nset_option Elab.async false\nset_option maxRecDepth 65536\nset_option maxHeartbeats 8000000\n\n'
    out+='abbrev nativeSetup := SubwordRows.nativeSetup\n\n'
    for col in range(9):
        full=f'Data.GKRSetup.SubwordMemory.setupColumn{col}';last=len(artifact['columns'][col]['blocks'])-1
        out+=f'theorem paddingPrefix{col} : (({full}.blocks.toList.take {last}).map Block.length).sum = 14286849 := by decide +kernel\n\n'
        out+=f'theorem paddingShape{col} : {full}.blocks[{last}] = Block.affine 2490367 0 0 := by rfl\n\n'
        out+=f'theorem paddingValue{col} (row : Fin 16777216) (lower : 14286849 ≤ row.val) : {full}.get? row.val = some 0 := by\n'
        out+=f'  have actual := column_block_value {full} ⟨{last}, by decide +kernel⟩ 14286849 row.val paddingPrefix{col} lower (by\n    rw [paddingShape{col}]\n    have := row.isLt\n    change row.val - 14286849 < 2490367\n    omega)\n'
        out+=f'  rw [paddingShape{col}] at actual\n  exact actual.trans (constant_block_get _ _ _ (by have := row.isLt; omega))\n\n'
    full='Data.GKRSetup.SubwordMemory.setupColumn8'
    out+=f'theorem decoderPrefix : (({full}.blocks.toList.take 7).map Block.length).sum = 13238273 := by decide +kernel\n\n'
    out+=f'theorem decoderShape : {full}.blocks[7] = Block.affine 1048576 46 0 := by rfl\n\n'
    out+='theorem decoder_tag (row : Fin nativeSetup.imported.data.length)\n    (lower : 13238273 ≤ row.val) (upper : row.val < 14286849) : nativeSetup.value row (.generic 8) = 46 := by\n'
    out+='  rw [nativeSetup.generic_cell_value row (⟨8, by decide⟩ : Fin 9)]\n  simp only [show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]\n'
    out+=f'  have actual := column_block_value {full} ⟨7, by decide +kernel⟩ 13238273 row.val decoderPrefix lower (by\n    rw [decoderShape]\n    change row.val - 13238273 < 1048576\n    omega)\n'
    out+='  rw [decoderShape] at actual\n  change (((Data.GKRSetup.SubwordMemory.setupColumn8.get? row.val).getD 0) : Source.BaseField) = 46\n  rw [actual, constant_block_get _ _ _ (by omega)]\n  rfl\n\n'
    out+='theorem padding_row (row : Fin 16777216) (lower : 14286849 ≤ row.val) :\n    SubwordRows.nativeRow row = Vector.replicate 9 0 := by\n  apply Vector.ext\n  intro column bound\n  simp only [SubwordRows.nativeRow, TableData.row, Vector.getElem_map, Vector.getElem_replicate,\n    show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add]\n  interval_cases column\n'
    for col in range(9):out+=f'  · change ((Setup.signedValue ((Data.GKRSetup.SubwordMemory.setupColumn{col}.get? row.val).getD 0)) : Source.BaseField) = 0\n    rw [paddingValue{col} row lower]\n    rfl\n'
    out+='\ntheorem full_table_refinement {query : Vector Source.BaseField 9}\n    (member : (nativeSetup.imported.data.table "Airbender.Native.SubwordMemory").Contains #[] query)\n    (notDecoder : query[8] ≠ 46) : (Verification.importedSubwordTable (p := babyBearModulus)).Contains #[] query := by\n'
    out+='  obtain ⟨row, equal⟩ := member\n  change query = SubwordRows.nativeRow row at equal\n  by_cases beforeDecoder : row.val < 13238273\n  · exact ⟨⟨row.val, beforeDecoder⟩, equal.trans (SubwordRows.prefix_row ⟨row.val, beforeDecoder⟩)⟩\n'
    out+='  · have lower : 14286849 ≤ row.val := by\n      by_contra earlier\n      have tag := decoder_tag row (by omega) (by omega)\n      apply notDecoder\n      rw [equal]\n      rw [nativeSetup.value_generic row (⟨8, by decide⟩ : Fin 9)] at tag\n      simpa only [SubwordRows.nativeRow, Vector.getElem_map] using tag\n'
    out+='    rw [padding_row row lower] at equal\n    refine ⟨⟨0, by decide⟩, equal.trans ?_⟩\n    decide +kernel\n\nend Airbender.Compiler.ROMNative.SubwordBoundary\n';return out


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for flag in ['write','check']:parser.add_argument('--'+flag,action='store_true')
    args=parser.parse_args();path=LEAN/'Airbender/Proofs/GKRProtocol/ROMNative/SubwordBoundary.lean';text=content()
    if args.check and (not path.exists() or path.read_text()!=text):raise ValueError('subword boundary scaffold changed')
    if args.write and (not path.exists() or path.read_text()!=text):path.write_text(text)
    print('Airbender.Proofs.GKRProtocol.ROMNative.SubwordBoundary')


if __name__=='__main__':main()
