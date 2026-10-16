#!/usr/bin/env python3
"""EIP-170 deployment gate and raw-transaction gas of the merged verifiers on a task-owned anvil.

Usage: merged_gas.py <2p21> <task-owned-port> <out.json> [data-root]
  The version's contracts root (l1_wrap_2p21/) must have built merged/ and merged_f1/ (forge build
  in each first). data-root defaults to the version's debug_data and must hold
  merged_calldata.hex, single_tx_f1.hex and verified_mark.hex.

Two anvil runs (Osaka, the compiler's EVM target):
  1. deployment gate, EIP-170 enforced: plain CREATE transactions from account 0 — SetupFrontier
     first (nonce 0, the F1 verifier's pinned frontier address), TestRegistry, the v0 verifier,
     the F1 verifier — each recorded as deployed (runtime size from eth_getCode) or rejected;
  2. measurement, code-size limit disabled when a verifier does not fit (recorded): the same
     deployments, then one raw transaction per verifier with the proof bytes as calldata.
Per tx: receipt gasUsed, calldata bytes / zero bytes / tokens, execution gas from the struct-log
trace (first.gas - (last.gas - last.gasCost)), the registry frame (callTracer), the returned
statement (must equal verified_mark.hex). The receipt is checked against
21000 + max(exec + 4*tokens, 10*tokens). Glamsterdam (EIP-7976) and Hegota prices are computed
from the same execution and bytes, not measured: 15000 + max(4*tokens + exec, 64*bytes) and
15000 + max(4*tokens + exec, 96*bytes).
"""
import json
import os
import pathlib
import socket
import subprocess
import sys
import time
import urllib.request

SCRIPT_DIR = pathlib.Path(__file__).resolve().parent
VERSIONS = {
    "2p21": (SCRIPT_DIR / "l1_wrap_2p21", SCRIPT_DIR.parent / "debug_data" / "l1_wrap_2p21"),
}
GAS_LIMIT = 16_000_000  # under Osaka's EIP-7825 per-transaction cap
EIP170 = 24_576
FRONTIER = "0x5fbdb2315678afecb367f032d93f642f64180aa3"


def rpc(url, method, params):
    body = json.dumps({"jsonrpc": "2.0", "id": 1, "method": method, "params": params}).encode()
    req = urllib.request.Request(url, body, {"Content-Type": "application/json"})
    with urllib.request.urlopen(req, timeout=600) as r:
        resp = json.loads(r.read())
    if "error" in resp:
        raise RuntimeError(f"{method}: {resp['error']}")
    return resp["result"]


def creation(path):
    return bytes.fromhex(json.loads(pathlib.Path(path).read_text())["bytecode"]["object"][2:])


def word(addr):
    return bytes.fromhex(addr[2:].rjust(64, "0"))


def tokens(data):
    z = data.count(0)
    return z + 4 * (len(data) - z), z


class Anvil:
    def __init__(self, port, size_limit):
        self.chain_id = 1_000_000_000 + os.getpid() + (0 if size_limit else 1)
        args = ["anvil", "--host", "127.0.0.1", "--hardfork", "osaka", "--steps-tracing",
                "--chain-id", str(self.chain_id), "--port", str(port), "--silent"]
        if not size_limit:
            args.append("--disable-code-size-limit")
        self.proc = subprocess.Popen(args)
        self.url = f"http://127.0.0.1:{port}"
        for _ in range(100):
            try:
                if int(rpc(self.url, "eth_chainId", []), 16) == self.chain_id:
                    break
            except OSError:
                time.sleep(0.1)
        else:
            self.close()
            raise SystemExit("anvil readiness timed out")
        self.sender = rpc(self.url, "eth_accounts", [])[0]

    def close(self):
        self.proc.terminate()
        self.proc.wait()

    def send(self, to, data):
        tx = {"from": self.sender, "gas": hex(GAS_LIMIT), "data": "0x" + data.hex()}
        if to:
            tx["to"] = to
        h = rpc(self.url, "eth_sendTransaction", [tx])
        for _ in range(600):
            rc = rpc(self.url, "eth_getTransactionReceipt", [h])
            if rc is not None:
                return h, rc
            time.sleep(0.1)
        raise SystemExit(f"no receipt for {h}")

    def deploy(self, name, init):
        h, rc = self.send(None, init)
        ok = int(rc["status"], 16) == 1
        addr = rc["contractAddress"] if ok else None
        code = rpc(self.url, "eth_getCode", [addr, "latest"]) if ok else "0x"
        return {"name": name, "tx": h, "deployed": ok, "address": addr,
                "runtime_bytes": (len(code) - 2) // 2, "initcode_bytes": len(init),
                "deploy_gas": int(rc["gasUsed"], 16)}


def main():
    if len(sys.argv) not in (4, 5) or sys.argv[1] not in VERSIONS:
        raise SystemExit("usage: merged_gas.py <2p21> <task-owned-port> <out.json> [data-root]")
    root, data_root = VERSIONS[sys.argv[1]]
    if len(sys.argv) == 5:
        data_root = pathlib.Path(sys.argv[4]).resolve()
    port, out = int(sys.argv[2]), pathlib.Path(sys.argv[3])
    with socket.socket() as probe:
        probe.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        probe.bind(("127.0.0.1", port))
    read = lambda name: bytes.fromhex((data_root / name).read_text().strip())
    v0_cd, f1_cd, mark = read("merged_calldata.hex"), read("single_tx_f1.hex"), read("verified_mark.hex")
    frontier_init = creation(root / "merged_f1/out/SetupFrontier.sol/SetupFrontier.json")
    registry_init = creation(root / "merged/out/TestRegistry.sol/TestRegistry.json")
    v0_init = creation(root / "merged/out/GkrWhirVerifier.sol/GkrWhirVerifier.json")
    f1_init = creation(root / "merged_f1/out/GkrWhirVerifier.sol/GkrWhirVerifier.json")

    def deploy_all(chain):
        frontier = chain.deploy("SetupFrontier", frontier_init)
        assert frontier["address"] == FRONTIER, "the frontier did not land at the pinned address"
        registry = chain.deploy("TestRegistry", registry_init)
        v0 = chain.deploy("GkrWhirVerifier (v0)", v0_init + word(registry["address"]))
        f1 = chain.deploy("GkrWhirVerifier (F1)", f1_init + word(registry["address"]))
        return [frontier, registry, v0, f1]

    results = {"contracts_root": str(root), "data_root": str(data_root), "eip170": EIP170}
    chain = Anvil(port, size_limit=True)
    try:
        results["deployment_gate"] = deploy_all(chain)
    finally:
        chain.close()
    needs_override = not all(d["deployed"] for d in results["deployment_gate"])
    results["measurement_code_size_limit_disabled"] = needs_override

    chain = Anvil(port, size_limit=not needs_override)
    try:
        deployments = deploy_all(chain)
        registry = deployments[1]["address"]

        def measure(name, to, data):
            h, rc = chain.send(to, data)
            assert int(rc["status"], 16) == 1, f"{name}: verification transaction reverted"
            t, z = tokens(data)
            calls = rpc(chain.url, "debug_traceTransaction", [h, {"tracer": "callTracer"}])
            logs = rpc(chain.url, "debug_traceTransaction",
                       [h, {"disableStack": True, "disableMemory": True, "disableStorage": True}])
            steps = logs["structLogs"]
            execution = steps[0]["gas"] - (steps[-1]["gas"] - steps[-1]["gasCost"])
            used = int(rc["gasUsed"], 16)
            model = 21000 + max(execution + 4 * t, 10 * t)
            standard = 4 * t + execution
            frames = [{"to": c["to"], "gasUsed": int(c["gasUsed"], 16)} for c in calls.get("calls", [])]
            registry_gas = sum(f["gasUsed"] for f in frames if f["to"].lower() == registry.lower())
            ret = bytes.fromhex(calls.get("output", "0x")[2:])
            assert ret == mark, f"{name}: returned statement differs from verified_mark.hex"
            return {"name": name, "tx": h, "gasUsed": used, "calldata_bytes": len(data),
                    "zero_bytes": z, "tokens": t, "standard_calldata_gas": 4 * t,
                    "floor_gas": 21000 + 10 * t, "execution_gas": execution,
                    "registry_frame_gas": registry_gas,
                    "verifier_execution_gas": execution - registry_gas,
                    "binding": "floor" if 10 * t >= execution + 4 * t else "execution",
                    "model_gas": model, "model_matches_receipt": model == used,
                    "glamsterdam_gas": 15000 + max(standard, 64 * len(data)),
                    "glamsterdam_floor_room": 64 * len(data) - standard,
                    "hegota_gas": 15000 + max(standard, 96 * len(data)),
                    "frames": frames}

        results["deployments"] = deployments
        results["v0"] = measure("v0", deployments[2]["address"], v0_cd)
        results["f1"] = measure("f1", deployments[3]["address"], f1_cd)
    finally:
        chain.close()

    out.write_text(json.dumps(results, indent=2) + "\n")
    for d in results["deployment_gate"]:
        verdict = "deployed" if d["deployed"] else "REJECTED"
        print(f"gate  {d['name']:22s} {verdict:9s} runtime {d['runtime_bytes']:>6,} B  "
              f"initcode {d['initcode_bytes']:>6,} B  deploy gas {d['deploy_gas']:>9,}")
    print(f"measurement anvil code-size limit disabled: {needs_override}")
    for k in ("v0", "f1"):
        r = results[k]
        print(f"{k:3s} gasUsed {r['gasUsed']:>9,}  bytes {r['calldata_bytes']:>7,}  zero {r['zero_bytes']:>5}  "
              f"exec {r['execution_gas']:>9,} (registry {r['registry_frame_gas']:,})  "
              f"Glamsterdam {r['glamsterdam_gas']:>9,}  room {r['glamsterdam_floor_room']:>9,}  "
              f"{r['binding']}  model==receipt {r['model_matches_receipt']}")
    bad = [k for k in ("v0", "f1") if not results[k]["model_matches_receipt"]]
    if bad:
        raise SystemExit(f"receipt gas differs from the model for {bad}")


if __name__ == "__main__":
    main()
