#!/usr/bin/env python3
"""Bind window-parametric full trace witnesses to actual row virtual setup."""
import argparse
import os
import subprocess
from export_gkr_translations import LEAN


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--mode',choices=['uncached','cached'],action='append')
    for flag in ['write','check','build']:parser.add_argument('--'+flag,action='store_true')
    args=parser.parse_args()
    for mode in args.mode or ['uncached','cached']:
        case='Unified'+mode.title()
        text=(LEAN/'scripts/templates/gkr_windowed_public.lean').read_text().replace('UnifiedUncached',case)
        target='Airbender.Proofs.GKRProtocol.WindowedNative.'+case+'Public';path=LEAN/(target.replace('.','/')+'.lean')
        if args.check and (not path.exists() or path.read_text()!=text):raise ValueError('windowed public bridge changed: '+case)
        if args.write:path.write_text(text)
        print(target,flush=True)
        if args.build:subprocess.run(['lake','--no-cache','build','+'+target+':olean'],cwd=LEAN,env=dict(os.environ,LEAN_NUM_THREADS='1'),check=True)


if __name__=='__main__':main()
