#!/usr/bin/env python3
"""Read complete helper lengths from the original data definitions."""
import argparse
import json
from pathlib import Path
import re
import subprocess
import tempfile
from gkr_packed_helper_validity import ALL_CASES, DIMENSIONS, fingerprint, inputs


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write',action='store_true')
    parser.add_argument('--check',action='store_true')
    args=parser.parse_args();entries={}
    with tempfile.TemporaryDirectory(prefix='helper-validity-dimensions-') as directory:
        for case in ALL_CASES:
            source=inputs(case)+f'''
set_option maxRecDepth 8192
#reduce Airbender.Compiler.HelperValidityNative.{case}.native.profile.protectedFields.length
#reduce Airbender.Compiler.HelperNative.{case}.native.fields.length
'''
            path=Path(directory)/(case+'.lean');path.write_text(source)
            result=subprocess.run(['lean','--tstack=32768',str(path)],text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
            if result.returncode:raise SystemExit(result.stdout[-1800:])
            values=[int(value) for value in re.findall(r'^([0-9]+)$',result.stdout,re.M)]
            if len(values)!=2:raise SystemExit('helper dimensions changed: '+case)
            entries[case]=dict(protected=values[0],fields=values[1],source_sha256=fingerprint(case))
    text=json.dumps(entries,indent=2)+'\n'
    if args.check and (not DIMENSIONS.exists() or DIMENSIONS.read_text()!=text):raise SystemExit('stale helper dimensions')
    if args.write:DIMENSIONS.parent.mkdir(parents=True,exist_ok=True);DIMENSIONS.write_text(text)
    print('PASS original helper dimensions:',len(entries))


if __name__=='__main__':main()
