#!/usr/bin/env python3
"""Check reproducibility of unified native-table proof data without trusting it."""
import os
import subprocess
from export_gkr_translations import LEAN
from gkr_unified_prefix import pilot


def main():
    commands=[
        ['gkr_unified_prefix.py','--column','1','--unit','8','--check'],
        ['gkr_unified_equal_chunks.py','--check'],
        ['gkr_unified_special_chunks.py','--check'],
        ['gkr_unified_chunk_lengths.py','--check'],
        ['gkr_unified_prefix_assembly.py','--stage','special','--check'],
        ['gkr_unified_prefix_assembly.py','--stage','column','--check'],
        ['gkr_unified_logical_regions.py','--check'],
        ['gkr_unified_rows.py','--check'],
        ['gkr_unified_rows.py','--rows','--check'],
        ['gkr_unified_boundary.py','--check'],
    ]
    # Column 1 uses separately bounded certificates for its large periodic spans.
    commands[0:1]=[['gkr_unified_prefix.py','--column','1','--unit',str(unit),'--check'] for unit in range(8,34)]
    _,part0=pilot(1,0,8,assemble=False)
    if (LEAN/'GKRProtocol/UnifiedPrefixParts/Column1/Part0.lean').read_text()!=part0:
        raise ValueError('unified prefix initial span scaffold changed')
    commands.insert(1,['gkr_unified_prefix.py','--column','1','--assembly','--check'])
    for command in commands:
        subprocess.run(['python3','scripts/'+command[0],*command[1:]],cwd=LEAN,
                       env=dict(os.environ,LEAN_NUM_THREADS='1'),check=True,stdout=subprocess.DEVNULL)
    print('PASS reproducible unified native-table proof scaffolds (kernel certificates checked separately)')


if __name__=='__main__':main()
