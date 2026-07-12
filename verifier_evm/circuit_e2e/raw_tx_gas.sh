#!/bin/bash
# Measure the REAL transaction gas of the GKR and WHIR verifiers by sending raw
# transactions (calldata = the proof) to anvil — no forge/Solidity harness, so the
# proof bytes are tx calldata (paid via intrinsic/EIP-7623), never memory-copied.
set -e
cd "$(dirname "$0")"
RPC=http://127.0.0.1:8545
KEY=0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80
GKR=0x0000000000000000000000000000000061110001
WHIR=0x0000000000000000000000000000000011170001
REG=0x00000000000000000000000000000000CafE0001

# start a fresh anvil on the Prague hardfork (EIP-7623 calldata floor)
pkill -f "anvil.*8545" 2>/dev/null || true
anvil --hardfork prague --port 8545 --silent &
ANVIL=$!
trap 'kill $ANVIL 2>/dev/null' EXIT
until cast block-number --rpc-url $RPC >/dev/null 2>&1; do sleep 0.3; done

# etch the precompiled runtime bytecode of all three contracts
cast rpc anvil_setCode $GKR  "0x$(cat gkr_runtime.hex)"      --rpc-url $RPC >/dev/null
cast rpc anvil_setCode $WHIR "0x$(cat whir_runtime.hex)"     --rpc-url $RPC >/dev/null
cast rpc anvil_setCode $REG  "0x$(cat registry_runtime.hex)" --rpc-url $RPC >/dev/null

gkr_cd="0x$(cat ../whir/testdata/gkr_full_calldata.hex)"
whir_cd="0x$(cat ../whir/testdata/proth120_whir_calldata_from_proof.hex)"

run() {
  local name="$1" addr="$2" cd="$3"
  # send raw tx; capture receipt gasUsed + status + logs
  local rc=$(cast send "$addr" "$cd" --private-key $KEY --rpc-url $RPC --json --gas-limit 30000000)
  local gasUsed=$(echo "$rc" | python3 -c 'import json,sys; print(int(json.load(sys.stdin)["gasUsed"],16))')
  local status=$(echo "$rc" | python3 -c 'import json,sys; print(json.load(sys.stdin)["status"])')
  local nlogs=$(echo "$rc" | python3 -c 'import json,sys; print(len(json.load(sys.stdin)["logs"]))')
  local commit=$(echo "$rc" | python3 -c 'import json,sys; l=json.load(sys.stdin)["logs"]; print(l[0]["topics"][1] if l else "none")')
  # calldata gas breakdown (EIP-7623): intrinsic 21000, floor = 21000 + 10*tokens
  local bytes=$(( (${#cd} - 2) / 2 ))
  python3 - "$name" "$gasUsed" "$status" "$nlogs" "$commit" "$cd" <<'PY'
import sys
name,gasUsed,status,nlogs,commit,cd=sys.argv[1:7]
cd=bytes.fromhex(cd[2:])
zero=sum(1 for b in cd if b==0); nz=len(cd)-zero
tokens=zero+4*nz
intrinsic=21000+16*nz+4*zero          # standard intrinsic (== 21000 + 4*tokens)
floor=21000+10*tokens                  # EIP-7623 calldata floor
g=int(gasUsed)
exe=g-intrinsic                        # execution the EVM actually ran
std_tx=intrinsic+exe                   # execution path
final=max(std_tx, floor)               # EIP-7623: tx pays the larger
bound = "CALLDATA-FLOOR (EIP-7623)" if floor>=std_tx else "EXECUTION"
print(f"== {name} verifier ==")
print(f"   status={status}  logs={nlogs}  committed={commit[:18]}...")
print(f"   calldata {len(cd)} B  ({nz} nz, {zero} z)  tokens={tokens:,}")
print(f"   execution gas (EVM ran)   = {exe:,}")
print(f"   intrinsic (21000+4*tokens)= {intrinsic:,}")
print(f"   EIP-7623 floor (10*tokens)= {floor:,}")
print(f"   => real tx gasUsed        = {final:,}   [{bound}-bound]")
PY
}

run GKR  $GKR  "$gkr_cd"
run WHIR $WHIR "$whir_cd"
