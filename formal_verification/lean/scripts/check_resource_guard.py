#!/usr/bin/env python3
"""Small owned parent/child probes; never allocate more than 96 MiB."""
from pathlib import Path
import json
import subprocess
import sys
import tempfile

GUARD = Path(__file__).with_name("bounded_fv.py")

def run():
    with tempfile.TemporaryDirectory(prefix="airbender-guard-") as directory:
        cases = [
            ("success", "pass", 10, 128, 256, "finished", 0),
            ("timeout", "import subprocess,time; subprocess.Popen(['sleep','10']); time.sleep(10)",
             0.35, 128, 256, "wall-time budget exceeded", 125),
            ("memory", "import subprocess,sys,time; subprocess.Popen([sys.executable,'-c',"
             "'import time; x=bytearray(96*1024*1024); time.sleep(10)']); time.sleep(10)",
             10, 48, 128, "memory budget exceeded", 125),
        ]
        for name, code, seconds, memory, resident, reason, expected in cases:
            result = subprocess.run([sys.executable, str(GUARD), "--mib", str(memory),
                "--resident-mib", str(resident), "--seconds", str(seconds), "--log",
                str(Path(directory) / (name + ".log")), "--", sys.executable, "-c", code],
                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            report = json.loads(result.stdout)
            assert result.returncode == expected and report["reason"] == reason, report
            assert report["live_owned_after"] == [], report
            if name != "success":
                assert len(report["owned_pids"]) >= 2, report
            print(f"PASS guard {name}; {report['seconds']}s; no live owned processes")

if __name__ == "__main__":
    run()
