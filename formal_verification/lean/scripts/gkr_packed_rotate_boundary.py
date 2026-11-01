#!/usr/bin/env python3
"""Check the complete fixed rotation-boundary source in unified column one."""
import argparse
import re
import subprocess
from gkr_unified_prefix import LEAN, pilot, plans

STEM = 'Airbender.Proofs.GKRProtocol.UnifiedFixedSpans.RotateBoundary'
OWNER = 'Airbender.Compiler.UnifiedFixedSpans.RotateBoundary'
LEGACY = 'Airbender.Compiler.UnifiedPrefixNative.Column1'


def modules():
    artifact, blocks, positions, _, groups, _ = plans(1)
    selected = groups[14]
    if positions[15]-positions[14] != 262144 or len(selected) != 12 or {
            artifact['tables'][entry['region']]['id'] if entry['region'] is not None else None
            for entry in selected} != {47,48,49,50,51}:
        raise ValueError('fixed rotation-boundary scope changed')
    _, old = pilot(1,14,15,assemble=False)
    data = old[:old.index('set_option maxHeartbeats 16000000 in')]
    data = re.sub(r'^set_option maxHeartbeats \d+\n', '', data, flags=re.M)
    data += 'end ' + LEGACY + '\n'
    yield STEM+'.Data',data

    header = (f'namespace {OWNER}\nopen Airbender Airbender.Compiler\n'
              'open PackedSetupEquality\nset_option warningAsError true\n'
              'set_option Elab.async false\nset_option maxRecDepth 131072\n\n')
    codes = (f'import {STEM}.Data\nimport Airbender.Import.PackedSetupEmbed\n'
             'import Airbender.Proofs.GKRProtocol.PackedSetupSpans\n\n' + header +
             '-- Read and verify all five fixed regions in one data command.\n'
             'set_option maxHeartbeats 2000000\n\n'
             'import_setup_code_capture from "artifacts/setup/unified.json" [\n'
             '  sourceCode := column 1 block_start 14 block_count 1 unpacked,\n')
    codes += ',\n'.join(f'  target{index} := region {artifact["tables"][entry["region"]]["id"]} column 1 block_start {entry["target"]} block_count 1 packed_bytes 0'
                        for index,entry in enumerate(selected)) + ']\n\n'
    codes += 'def targetsCode : List BlockCode := ' + ' ++ '.join(f'target{i}' for i in range(12)) + '\n\n'
    codes += 'def requests : List PackedSetupSpans.Request := [⟨sourceCode.get ⟨0, by decide +kernel⟩, targetsCode⟩]\n\nend '+OWNER+'\n'
    yield STEM+'.Codes',codes

    bindings = (f'import {STEM}.Codes\nimport Airbender.Import.GKRProtocol.NumericArithmeticDataImport\n\n'+header+
                f'numeric_data_binding source_binding : {LEGACY}.source14 = (sourceCode.get ⟨0, by decide +kernel⟩).decode\n'
                f'numeric_data_binding targets_binding : {LEGACY}.target14 = targetsCode.map BlockCode.decode\n\nend '+OWNER+'\n')
    yield STEM+'.Bindings',bindings

    certificate = (f'import {STEM}.Bindings\n\n'+header+
                   'theorem checked : PackedSetupSpans.check requests = true := by decide +kernel\n\n'
                   f'theorem facts : ({LEGACY}.target14.map Setup.Block.length).sum = {LEGACY}.source14.length ∧\n'
                   f'    blockTargetsFollow {LEGACY}.source14 0 {LEGACY}.target14 := by\n'
                   '  rw [source_binding, targets_binding]\n'
                   '  exact PackedSetupSpans.check_sound_at requests checked ⟨0, by decide +kernel⟩\n\nend '+OWNER+'\n')
    yield STEM+'.Certificate',certificate
    projected = (f'import {STEM}.Certificate\n\nnamespace {LEGACY}\nopen Airbender Airbender.Compiler\n'
                 'set_option warningAsError true\nset_option Elab.async false\n\n'
                 f'theorem follows14 : blockTargetsFollow source14 0 target14 := {OWNER}.facts.2\n\n'
                 f'theorem length14 : (target14.map Setup.Block.length).sum = source14.length := {OWNER}.facts.1\n\n'
                 'end '+LEGACY+'\n')
    yield 'Airbender.Proofs.GKRProtocol.UnifiedPrefixParts.Column1.Unit14',projected


def preflight(generated):
    for name,source in generated:
        path=LEAN/(name.replace('.','/')+'.lean')
        if path.exists() and path.read_text()!=source and subprocess.run(
                ['git','ls-files','--error-unmatch',str(path.relative_to(LEAN))],cwd=LEAN,
                stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode:
            raise ValueError('refuse to replace untracked capture source: '+str(path))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write',action='store_true')
    parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    generated=list(modules())
    if args.write:preflight(generated)
    for name,source in generated:
        path=LEAN/(name.replace('.','/')+'.lean')
        if args.check and (not path.exists() or path.read_text()!=source):
            raise ValueError('fixed rotation-boundary capture changed: '+name)
        if args.write and (not path.exists() or path.read_text()!=source):
            path.parent.mkdir(parents=True,exist_ok=True);path.write_text(source)
        print(name)


if __name__=='__main__':
    main()
