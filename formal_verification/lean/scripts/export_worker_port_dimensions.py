#!/usr/bin/env python3
"""Read worker vector lengths from the complete original Lean source."""
import argparse
import json
from pathlib import Path
import re
import subprocess
import tempfile
from gkr_packed_worker_ports import CASES, DIMENSIONS, fingerprint, identity, input_text


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write',action='store_true')
    parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    entries={}
    with tempfile.TemporaryDirectory(prefix='worker-port-dimensions-') as directory:
        for case in CASES:
            _,_,model=identity(case)
            memory='Airbender.Compiler.MemoryNative.'+case+'.native'
            source=input_text(case)+f'''
set_option maxRecDepth 8192
#reduce Airbender.Compiler.WorkerPortsNative.{case}.originalIndices.length + 2 * Airbender.{model}.importedConstraintsMemoryPorts.size
#reduce (({memory}.memoryReadRows ++ {memory}.memoryWriteRows).flatMap (fun row => row.fields.flatMap (fun field => field.historyIndices))).length
'''
            path=Path(directory)/(case+'.lean');path.write_text(source)
            result=subprocess.run(['lean','--tstack=32768',str(path)],text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
            if result.returncode:raise SystemExit(result.stdout[-1800:])
            sizes=[int(value) for value in re.findall(r'^([0-9]+)$',result.stdout,re.M)]
            if len(sizes)!=2:raise SystemExit('worker dimension output changed: '+case)
            entries[case]=dict(columns=sizes[0],bounds=sizes[1],source_sha256=fingerprint(case))
    text=json.dumps(entries,indent=2)+'\n'
    if args.check and (not DIMENSIONS.exists() or DIMENSIONS.read_text()!=text):raise SystemExit('stale worker dimensions')
    if args.write:DIMENSIONS.parent.mkdir(parents=True,exist_ok=True);DIMENSIONS.write_text(text)
    print('PASS original worker vector dimensions:',len(entries))


if __name__=='__main__':main()
