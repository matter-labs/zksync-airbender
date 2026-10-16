#!/usr/bin/env python3
"""Raw-transaction gas for the two-tx pair and the single-tx proxy on a task-owned anvil (Prague).

Usage: single_tx_gas.py <2p21> <task-owned-port> <out.json> [data-root]
  The version's contracts root (l1_wrap_2p21/) must have built gkr/, whir/, two_tx/,
  single_tx/{gkr,whir,harness}/ and single_tx/f1/{gkr,whir}/ (forge build in each first). data-root
  defaults to the version's debug_data and must hold gkr_full_calldata.hex,
  proth120_whir_calldata_from_proof.hex, single_tx_f1.hex and single_tx_f1_fields.json.
  Transactions: the two-tx pair, the v0 single-tx proxy and the F1 single-tx proxy.

Proof bytes are tx calldata (intrinsic / EIP-7623). Per tx: receipt gasUsed, calldata bytes /
zero bytes / tokens, execution gas from the struct-log trace (first.gas - (last.gas - last.gasCost)),
and the callTracer frames. The receipt is checked against 21000 + max(exec + 4*tokens, 10*tokens).
Glamsterdam (EIP-7976) and Hegota prices are computed from the same execution and bytes, not
measured: 15000 + max(4*tokens + exec, 64*bytes) and 15000 + max(4*tokens + exec, 96*bytes).
For the single tx, the proxy artefact = execution - sum of the GKR and WHIR frames' gasUsed
(calldata/returndata copies into memory, memory expansion, CALL overhead, the commitment compare).
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
GAS_LIMIT = 25_000_000
GKR2 = "0x0000000000000000000000000000000061110001"
WHIR2 = "0x0000000000000000000000000000000011170001"
REG = "0x00000000000000000000000000000000CafE0001"
GKR1 = "0x00000000000000000000000000000000611b0002"
WHIR1 = "0x0000000000000000000000000000000011170002"
GKR_F1 = "0x00000000000000000000000000000000611b0012"
WHIR_F1 = "0x0000000000000000000000000000000011170012"
FRONTIER = "0x000000000000000000000000000000005e7f0001"


def rpc(url, method, params):
    body = json.dumps({"jsonrpc": "2.0", "id": 1, "method": method, "params": params}).encode()
    req = urllib.request.Request(url, body, {"Content-Type": "application/json"})
    with urllib.request.urlopen(req, timeout=600) as r:
        resp = json.loads(r.read())
    if "error" in resp:
        raise RuntimeError(f"{method}: {resp['error']}")
    return resp["result"]


def artifact(path):
    j = json.loads(pathlib.Path(path).read_text())
    return j["bytecode"]["object"], j["deployedBytecode"]["object"]


def word(x):
    return x.to_bytes(32, "big").hex() if isinstance(x, int) else x[2:].lower().rjust(64, "0")


def tokens(data):
    z = data.count(0)
    return z + 4 * (len(data) - z), z


def main():
    if len(sys.argv) not in (4, 5) or sys.argv[1] not in VERSIONS:
        raise SystemExit("usage: single_tx_gas.py <2p21> <task-owned-port> <out.json> [data-root]")
    root, data_root = VERSIONS[sys.argv[1]]
    if len(sys.argv) == 5:
        data_root = pathlib.Path(sys.argv[4]).resolve()
    port, out = int(sys.argv[2]), pathlib.Path(sys.argv[3])
    with socket.socket() as probe:
        probe.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        probe.bind(("127.0.0.1", port))
    gkr = bytes.fromhex((data_root / "gkr_full_calldata.hex").read_text().strip())
    whir = bytes.fromhex((data_root / "proth120_whir_calldata_from_proof.hex").read_text().strip())

    chain_id = 1_000_000_000 + os.getpid()
    anvil = subprocess.Popen(
        ["anvil", "--host", "127.0.0.1", "--hardfork", "prague", "--steps-tracing",
         "--chain-id", str(chain_id), "--port", str(port), "--gas-limit", "100000000", "--silent"])
    url = f"http://127.0.0.1:{port}"
    try:
        for _ in range(100):
            try:
                if int(rpc(url, "eth_chainId", []), 16) == chain_id:
                    break
            except OSError:
                time.sleep(0.1)
        else:
            raise SystemExit("anvil readiness timed out")
        sender = rpc(url, "eth_accounts", [])[0]

        def send(to, data):
            tx = {"from": sender, "gas": hex(GAS_LIMIT), "data": "0x" + data.hex()}
            if to:
                tx["to"] = to
            h = rpc(url, "eth_sendTransaction", [tx])
            for _ in range(600):
                rc = rpc(url, "eth_getTransactionReceipt", [h])
                if rc is not None:
                    break
                time.sleep(0.1)
            else:
                raise SystemExit(f"no receipt for {h}")
            if int(rc["status"], 16) != 1:
                raise SystemExit(f"tx to {to} failed")
            return h, rc

        def deploy(creation, args=""):
            _, rc = send(None, bytes.fromhex(creation[2:] + args))
            return rc["contractAddress"]

        def set_code(addr, code):
            rpc(url, "anvil_setCode", [addr, code])

        def selector(sig):
            return subprocess.check_output(["cast", "sig", sig], text=True).strip()[2:]

        _, gkr2_code = artifact(root / "gkr/out/GkrVerifier.sol/GKRVerifier.json")
        _, whir2_code = artifact(root / "whir/out/WhirVerifier.sol/WhirVerifier.json")
        _, gkr1_code = artifact(root / "single_tx/gkr/out/GkrVerifier.sol/GKRVerifier.json")
        _, gkr_f1_code = artifact(root / "single_tx/f1/gkr/out/GkrVerifier.sol/GKRVerifier.json")
        _, whir_f1_code = artifact(root / "single_tx/f1/whir/out/WhirVerifier.sol/WhirVerifier.json")
        _, whir1_code = artifact(root / "single_tx/whir/out/WhirVerifier.sol/WhirVerifier.json")
        reg_init, _ = artifact(root / "two_tx/out/GkrWhirRegistry.sol/GkrWhirRegistry.json")
        wrap_init, _ = artifact(
            root / "single_tx/harness/out/L1VerifierSingleTx.sol/L1VerifierSingleTx.json")
        for a, c in [(GKR2, gkr2_code), (WHIR2, whir2_code), (GKR1, gkr1_code), (WHIR1, whir1_code),
                     (GKR_F1, gkr_f1_code), (WHIR_F1, whir_f1_code)]:
            set_code(a, c)
        reg_impl = deploy(reg_init, word(sender))
        set_code(REG, rpc(url, "eth_getCode", [reg_impl, "latest"]))
        send(REG, bytes.fromhex(selector("initialize_verifiers(address,address)") + word(GKR2) + word(WHIR2)))
        wrapper = deploy(wrap_init, word(GKR1) + word(WHIR1) + word(len(gkr)))
        frontier_artifact = root / "single_tx/f1/frontier/out/SetupFrontier.sol/SetupFrontier.json"
        frontier_deploy_gas = None
        if frontier_artifact.exists():
            frontier_init, _ = artifact(frontier_artifact)
            h, rc = send(None, bytes.fromhex(frontier_init[2:]))
            frontier_deploy_gas = int(rc["gasUsed"], 16)
            set_code(FRONTIER, rpc(url, "eth_getCode", [rc["contractAddress"], "latest"]))
        f1 = bytes.fromhex((data_root / "single_tx_f1.hex").read_text().strip())
        f1_gkr_bytes = json.loads((data_root / "single_tx_f1_fields.json").read_text())["gkr_bytes"]
        wrapper_f1 = deploy(wrap_init, word(GKR_F1) + word(WHIR_F1) + word(f1_gkr_bytes))

        ret = bytes.fromhex(rpc(url, "eth_call", [{"to": GKR1, "data": "0x" + gkr.hex(),
                                                    "gas": hex(GAS_LIMIT)}, "latest"])[2:])
        plen = len(ret) - 96
        assert plen > 0 and ret[:plen] == whir[:plen], "single-tx GKR preimage != WHIR calldata prefix"
        single = gkr + whir[plen:]

        def measure(name, to, data):
            h, rc = send(to, data)
            t, z = tokens(data)
            calls = rpc(url, "debug_traceTransaction", [h, {"tracer": "callTracer"}])
            logs = rpc(url, "debug_traceTransaction",
                       [h, {"disableStack": True, "disableMemory": True, "disableStorage": True}])
            steps = logs["structLogs"]
            top = [s for s in steps if s["depth"] == 1]
            execution = top[0]["gas"] - (top[-1]["gas"] - top[-1]["gasCost"])
            used = int(rc["gasUsed"], 16)
            model = 21000 + max(execution + 4 * t, 10 * t)
            standard = 4 * t + execution
            frames = [{"to": c["to"], "gas": int(c["gas"], 16), "gasUsed": int(c["gasUsed"], 16),
                       "input_bytes": (len(c.get("input", "0x")) - 2) // 2,
                       "output_bytes": (len(c.get("output", "0x")) - 2) // 2}
                      for c in calls.get("calls", [])]
            r = {"name": name, "tx": h, "status": rc["status"], "gasUsed": used,
                 "calldata_bytes": len(data), "zero_bytes": z, "tokens": t,
                 "standard_calldata_gas": 4 * t, "floor_gas": 21000 + 10 * t,
                 "execution_gas": execution, "execution_headroom_below_floor": 6 * t - execution,
                 "binding": "floor" if 10 * t >= execution + 4 * t else "execution",
                 "model_gas": model, "model_matches_receipt": model == used,
                 "glamsterdam_gas": 15000 + max(standard, 64 * len(data)),
                 "glamsterdam_floor_room": 64 * len(data) - standard,
                 "hegota_gas": 15000 + max(standard, 96 * len(data)),
                 "callTracer_top_gasUsed": int(calls["gasUsed"], 16), "frames": frames,
                 "struct_steps": len(steps)}
            if frames:
                r["own_execution_gas"] = execution - sum(f["gasUsed"] for f in frames)
                own = {}
                for s in top:
                    own[s["op"]] = own.get(s["op"], 0) + s["gasCost"]
                r["top_frame_opcode_gasCost"] = dict(sorted(own.items(), key=lambda kv: -kv[1]))
            return r

        results = {
            "contracts_root": str(root), "data_root": str(data_root), "whir_preimage_bytes": plen,
            "two_tx_gkr": measure("two_tx_gkr", GKR2, gkr),
            "two_tx_whir": measure("two_tx_whir", WHIR2, whir),
            "single_tx": measure("single_tx", wrapper, single),
            "single_tx_f1": measure("single_tx_f1", wrapper_f1, f1),
        }
        s, g2, w2 = results["single_tx"], results["two_tx_gkr"], results["two_tx_whir"]
        gf, wf = s["frames"]
        results["summary"] = {
            "two_tx_total_gas": g2["gasUsed"] + w2["gasUsed"],
            "single_tx_gas": s["gasUsed"],
            "single_tx_bytes": s["calldata_bytes"],
            "single_tx_glamsterdam_gas": s["glamsterdam_gas"],
            "single_tx_glamsterdam_floor_room": s["glamsterdam_floor_room"],
            "single_tx_hegota_gas": s["hegota_gas"],
            "single_tx_binding": s["binding"],
            "single_tx_execution": s["execution_gas"],
            "single_tx_execution_headroom_below_floor": s["execution_headroom_below_floor"],
            "single_tx_gkr_frame": gf["gasUsed"], "single_tx_whir_frame": wf["gasUsed"],
            "proxy_artefact_gas": s["own_execution_gas"],
            "single_tx_execution_without_proxy_artefact": gf["gasUsed"] + wf["gasUsed"],
            "two_tx_execution_sum": g2["execution_gas"] + w2["execution_gas"],
            "removed_handoff_execution": g2["execution_gas"] + w2["execution_gas"]
            - gf["gasUsed"] - wf["gasUsed"],
            "f1_bytes": results["single_tx_f1"]["calldata_bytes"],
            "f1_zero_bytes": results["single_tx_f1"]["zero_bytes"],
            "f1_tokens": results["single_tx_f1"]["tokens"],
            "f1_execution": results["single_tx_f1"]["execution_gas"],
            "f1_gkr_frame": results["single_tx_f1"]["frames"][0]["gasUsed"],
            "f1_whir_frame": results["single_tx_f1"]["frames"][1]["gasUsed"],
            "f1_prague_gas": results["single_tx_f1"]["gasUsed"],
            "f1_glamsterdam_gas": results["single_tx_f1"]["glamsterdam_gas"],
            "f1_glamsterdam_floor_room": results["single_tx_f1"]["glamsterdam_floor_room"],
            "f1_hegota_gas": results["single_tx_f1"]["hegota_gas"],
            "setup_frontier_deploy_gas": frontier_deploy_gas,
        }
        out.write_text(json.dumps(results, indent=2) + "\n")
        for k in ("two_tx_gkr", "two_tx_whir", "single_tx", "single_tx_f1"):
            r = results[k]
            print(f"{k:12s} gasUsed {r['gasUsed']:>9,}  bytes {r['calldata_bytes']:>7,}  zero "
                  f"{r['zero_bytes']:>4}  tokens {r['tokens']:>7,}  exec {r['execution_gas']:>9,}  "
                  f"floor-headroom {r['execution_headroom_below_floor']:>8,}  {r['binding']}  "
                  f"model==receipt {r['model_matches_receipt']}")
        print(json.dumps(results["summary"], indent=2))
        mismatched = [k for k in ("two_tx_gkr", "two_tx_whir", "single_tx", "single_tx_f1")
                      if not results[k]["model_matches_receipt"]]
        if mismatched:
            raise SystemExit(f"receipt gas differs from the model for {mismatched}")
    finally:
        anvil.terminate()
        anvil.wait()


if __name__ == "__main__":
    main()
