#!/usr/bin/env python3
"""Bind constant native setup tags and aligned retained fixed-table columns."""
import argparse
import json
import os
import subprocess
from export_gkr_translations import LEAN

SPECS = {
    'jump-branch': ('JumpBranch', [(1, 'regZeroData', 0, 1), (2, 'jumpCleanupData', 1, 2),
                                 (5, 'signData', 2, 3), (31, 'conditionalData', 3, 4)]),
    'mul-div': ('MulDiv', [(1, 'regZeroData', 0, 1), (41, 'lowByteData', 3, 4)]),
}


def module(family, case, entries):
    ns='Airbender.Compiler.FixedSetupNative.'+case
    native='Airbender.Compiler.MaterializedNative.'+case+'Uncached.native.model'
    text=(f'import Airbender.Proofs.GKRProtocol.ColumnSlices\nimport Airbender.Proofs.GKRProtocol.TaggedSetup\nimport Airbender.Proofs.GKRProtocol.MaterializedNative.{case}Uncached\n'
          'import Airbender.Review.Helpers.Tables.PairData\n\n'+f'namespace {ns}\nopen Airbender Airbender.Compiler\n'
          'set_option warningAsError true\nset_option Elab.async false\nset_option maxRecDepth 65536\nset_option maxHeartbeats 4000000\n\n'
          f'abbrev nativeSetup := {native}\n\n')
    artifact=json.loads((LEAN / 'artifacts/setup' / (family + '.json')).read_text())
    for tag,target,start,stop in entries:
     region=next(r for r in artifact['tables'] if r['id']==tag)
     for col,a,b in [(0,start,stop)]+([(1,5,52)] if tag==31 else []):
      stem=target+str(col)
      full=f'nativeSetup.imported.data.columns[{col}]'
      dest=f'Verification.{target}.columns[{col}]'
      text+=(f'def {stem}Front : List Setup.Block := {full}.blocks.toList.take {a}\n'
             f'def {stem}Back : List Setup.Block := {full}.blocks.toList.drop {b}\n\n'
             f'theorem {stem}Shape : {full}.blocks.toList =\n'
             f'    {stem}Front ++ ({dest}.blocks.toList ++ {stem}Back) := by decide +kernel\n\n'
             f'theorem {stem}Prefix : ({stem}Front.map Setup.Block.length).sum = {region["offset"]} := by decide +kernel\n\n'
             f'theorem {stem}Length : ({dest}.blocks.toList.map Setup.Block.length).sum = {region["length"]} := by decide +kernel\n\n'
             f'theorem {stem}_value (index : Fin Verification.{target}.length) :\n'
             f'    {full}.get? ({region["offset"]} + index.val) = {dest}.get? index.val :=\n'
             f'  column_slice_value {full} {dest} {stem}Front {stem}Back {region["offset"]} {region["length"]}\n'
             f'    {stem}Shape {stem}Prefix {stem}Length index.val index.isLt\n\n')
    width=len(artifact['columns'])
    segments=[]
    for block in artifact['columns'][-1]['blocks']:
     if block['kind'] != 'affine' or block['step'] != 0:
      raise ValueError('unsupported constant tag encoding')
     segments.append((block['length'],block['first']))
    text += ('def tagSegments : List (Nat × Nat) :=\n  [' + ', '.join(f'({length}, {tag})' for length,tag in segments) + ']\n\n'
             f'theorem tag_shape : nativeSetup.imported.data.columns[{width-1}].blocks.toList =\n'
             '    tagSegments.map (fun entry => Setup.Block.affine entry.1 entry.2 0) := by decide +kernel\n\n'
             'theorem tag_value (row : Fin nativeSetup.imported.data.length) :\n'
             f'    nativeSetup.value row (.generic {width-1}) = constantTagValue tagSegments row.val := by\n'
             f'  have bridge := nativeSetup.constant_tag_value (⟨{width-1}, by decide⟩ : Fin {width}) tagSegments tag_shape row\n'
             '  simpa only [show nativeSetup.imported.data.offset = 0 from rfl, Nat.zero_add] using bridge\n\n')
    offset=0
    for length,tag in segments:
     text += (f'theorem tag{tag}_region (row : Fin nativeSetup.imported.data.length)\n'
              f'    (selected : nativeSetup.value row (.generic {width-1}) = {tag}) :\n'
              f'    {offset} ≤ row.val ∧ row.val < {offset+length} := by\n'
              f'  have rowBound : row.val < {artifact["trace_len"]} := row.isLt\n'
              '  rw [tag_value] at selected\n  simp only [tagSegments, constantTagValue] at selected\n'
              '  split_ifs at selected\n  all_goals first\n    | omega\n' +
              ''.join(f'    | exact False.elim ((by decide +kernel : ({other} : Source.BaseField) ≠ {tag}) selected)\n'
                      for _,other in segments if other != tag) + '\n')
     offset+=length
    text+='end '+ns+'\n'

    return 'Airbender.Proofs.GKRProtocol.FixedSetupNative.' + case, text


def membership_module(family, case, raw_entries):
    artifact = json.loads((LEAN / 'artifacts/setup' / (family + '.json')).read_text())
    definitions = {
        1: ('regIsZeroTable', 'Airbender.RegIsZero', 2),
        2: ('jumpCleanupTable', 'Airbender.JumpCleanupOffset', 3),
        5: ('u16SignTable', 'Airbender.U16GetSign', 2),
        31: ('conditionalTable', 'Airbender.ConditionalJmpBranchSlt', 2),
        41: ('u16LowByteTable', 'Airbender.U16GetLowByte', 2),
    }
    entries = []
    for tag, data, _, _ in raw_entries:
        table, label, arity = definitions[tag]
        region = next(item for item in artifact['tables'] if item['id'] == tag)
        entries.append((tag, data, table, label, region['offset'], region['length'], arity))
    width = len(artifact['columns'])
    ns='Airbender.Compiler.FixedSetupNative.'+case
    text=(f'import Airbender.Proofs.GKRProtocol.FixedMembership\nimport Airbender.Proofs.GKRProtocol.FixedSetupNative.{case}Values\n'
          'import Airbender.Review.Circuits.JumpBranchSlt.Tables.Control\nimport Airbender.Proofs.Tables.ImportedRanges\n\n'
          f'namespace {ns}\nopen Airbender Airbender.Compiler\n'
          'set_option warningAsError true\nset_option Elab.async false\nset_option maxRecDepth 65536\nset_option maxHeartbeats 4000000\n\n')
    for tag,data,table,label,offset,length,arity in entries:
     cols=', '.join(f'nativeSetup.value row (.generic {c})' for c in range(arity))
     tuple_type=' × '.join(['Source.BaseField']*arity)
     text+=(f'theorem tag{tag}_contains (row : Fin nativeSetup.imported.data.length)\n'
            f'    (selected : nativeSetup.value row (.generic {width-1}) = {tag})\n'
            f'    (provided : Array ({tuple_type})) :\n'
            f'    (Verification.{table} (p := babyBearModulus)).Contains provided ({cols}) := by\n'
            f'  have domain := tag{tag}_region row selected\n'
            f'  let index : Fin Verification.{data}.length := ⟨row.val - {offset}, by change row.val - {offset} < {length}; omega⟩\n'
            f'  have position : row.val = {offset} + index.val := by dsimp [index]; omega\n'
            f'  exact materialized_{"pair" if arity==2 else "triple"}_contains nativeSetup Verification.{data} (by decide) (by decide)\n'
            f'    {offset} rfl rfl row index position '+ ' '.join(('(fun entry => by change nativeValueColumn.get? (0 + entry.val) = zeroValueColumn.get? entry.val; rw [Nat.zero_add]; exact '+data+str(c)+'_value entry)') if offset==0 and c==1 else data+str(c)+'_value' for c in range(arity))+f' "{label}" provided\n\n')
    if case=='MulDiv':
     text+=r'''theorem range13_value_bound (row : Fin nativeSetup.imported.data.length)
    (selected : nativeSetup.value row (.generic 8) = 26) :
    (nativeSetup.value row (.generic 0)).val < 8192 := by
  have domain := tag26_region row selected
  let index : Fin 8192 := ⟨row.val - 196608, by omega⟩
  have position : row.val = 196608 + index.val := by dsimp [index]; omega
  have cell := nativeSetup.generic_cell_value row (⟨0, by decide⟩ : Fin 9)
  change nativeSetup.value row (.generic 0) =
    ((nativeKeyColumn.get? (0 + row.val)).getD 0 : Source.BaseField) at cell
  rw [Nat.zero_add, position, range13_key_value index, Option.getD_some] at cell
  rw [cell, ZMod.val_natCast, Nat.mod_eq_of_lt]
  · exact index.isLt
  · have bound := index.isLt
    have large : 8192 < babyBearModulus := by decide +kernel
    exact lt_trans bound large

'''
    text+='end '+ns+'\n'
    return 'Airbender.Proofs.GKRProtocol.FixedSetupNative.' + case + 'Membership', text


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--family', choices=SPECS, action='append')
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--build', action='store_true')
    args = parser.parse_args()
    for family, (case, entries) in SPECS.items():
        if args.family and family not in args.family:
            continue
        for target, text in [module(family, case, entries), membership_module(family, case, entries)]:
            path = LEAN / (target.replace('.', '/') + '.lean')
            if args.check and (not path.exists() or path.read_text() != text):
                raise ValueError('fixed setup tag/column binding changed: ' + target)
            if args.write and (not path.exists() or path.read_text() != text):
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text)
            print(target, flush=True)
            if args.build:
                subprocess.run(['lake', '--no-cache', 'build', '+' + target + ':olean'], cwd=LEAN,
                               env=dict(os.environ, LEAN_NUM_THREADS='1'), check=True)


if __name__ == '__main__':
    main()
