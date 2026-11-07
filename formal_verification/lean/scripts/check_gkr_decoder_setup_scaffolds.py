#!/usr/bin/env python3
"""Check reproducible native decoder-tail and query-adapter proof scaffolds."""
import subprocess
import sys
from export_gkr_translations import LEAN


def main():
    for script in ['gkr_unified_decoder_tail.py','gkr_decoder_tail_instances.py',
                   'gkr_decoder_tail_rows.py','gkr_decoder_membership_instances.py',
                   'gkr_decoder_query_instances.py']:
        subprocess.run([sys.executable,'scripts/'+script,'--check'],cwd=LEAN,check=True,
                       stdout=subprocess.DEVNULL)
    print('PASS reproducible native decoder setup/query scaffolds; kernel checking remains separate')

if __name__=='__main__':main()
