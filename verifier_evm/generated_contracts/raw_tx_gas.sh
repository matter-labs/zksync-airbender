#!/bin/sh
# Real per-transaction gas for the generated GKR + WHIR verifiers, measured with RAW anvil
# transactions (proof bytes are tx calldata, paid via intrinsic/EIP-7623 — never memory-copied,
# so no forge-harness over-count). Reads the compiled deployedBytecode from the sibling projects'
# out/ and calldata from the selected version's data root, or from [data-root] (e.g. a fresh
# proof's calldata). Prereq: build gkr/, whir/, and two_tx/ for that version.
# Usage: raw_tx_gas.sh <2p21> <task-owned-port> [data-root].
set -eu
SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
. "$SCRIPT_DIR/version.sh"
select_version "${1:?usage: raw_tx_gas.sh <2p21> <anvil-port> [data-root]}"
PORT=${2:?usage: raw_tx_gas.sh <2p21> <anvil-port> [data-root]}
if [ -n "${3:-}" ]; then
  DATA_ROOT=$(CDPATH= cd -- "$3" && pwd)
fi
case "$PORT" in *[!0-9]*|'') echo "invalid anvil port: $PORT" >&2; exit 2 ;; esac
# Fail before touching RPC state if any service already owns this port.
python3 - "$PORT" <<'PYPORT'
import socket, sys
port = int(sys.argv[1])
if not 1 <= port <= 65535:
    raise SystemExit("anvil port must be in 1..65535")
with socket.socket() as probe:
    probe.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    probe.bind(("127.0.0.1", port))
PYPORT
cd "$CONTRACTS_ROOT"
RPC=http://127.0.0.1:$PORT
KEY=0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80
GKR=0x0000000000000000000000000000000061110001
WHIR=0x0000000000000000000000000000000011170001
REG=0x00000000000000000000000000000000CafE0001

gkr_code=$(jq -r '.deployedBytecode.object' gkr/out/GkrVerifier.sol/GKRVerifier.json)
whir_code=$(jq -r '.deployedBytecode.object' whir/out/WhirVerifier.sol/WhirVerifier.json)

echo "== deployed bytecode sizes =="
printf "  GKR  verifier : %d bytes\n" $(( (${#gkr_code} - 2) / 2 ))
printf "  WHIR verifier : %d bytes\n" $(( (${#whir_code} - 2) / 2 ))

CHAIN_ID=$((1000000000 + $$))
anvil --host 127.0.0.1 --hardfork prague --chain-id "$CHAIN_ID" --port "$PORT" --silent &
ANVIL=$!
cleanup() {
  kill "$ANVIL" 2>/dev/null || true
  wait "$ANVIL" 2>/dev/null || true
}
trap cleanup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
attempt=0
while :; do
  kill -0 "$ANVIL" 2>/dev/null || { echo "anvil exited before readiness" >&2; exit 1; }
  if actual_chain=$(cast chain-id --rpc-url "$RPC" 2>/dev/null); then
    [ "$actual_chain" = "$CHAIN_ID" ] || {
      echo "RPC chain ID $actual_chain does not match owned anvil $CHAIN_ID" >&2; exit 1;
    }
    kill -0 "$ANVIL" 2>/dev/null || { echo "owned anvil exited" >&2; exit 1; }
    break
  fi
  attempt=$((attempt + 1))
  [ "$attempt" -lt 100 ] || { echo "anvil readiness timed out" >&2; exit 1; }
  sleep 0.1
done

cast rpc anvil_setCode $GKR  "$gkr_code"  --rpc-url $RPC >/dev/null
cast rpc anvil_setCode $WHIR "$whir_code" --rpc-url $RPC >/dev/null
# Run the constructor so the copied runtime contains the trusted initializer.
initializer=$(cast wallet address --private-key "$KEY")
reg_impl=$(cd two_tx && forge create src/GkrWhirRegistry.sol:GkrWhirRegistry \
  --broadcast --private-key "$KEY" --rpc-url "$RPC" --json --constructor-args "$initializer" \
  | jq -er '.deployedTo')
reg_code=$(cast code "$reg_impl" --rpc-url "$RPC")
printf "  Registry      : %d bytes\n" $(( (${#reg_code} - 2) / 2 ))
cast rpc anvil_setCode $REG  "$reg_code"  --rpc-url $RPC >/dev/null
cast send "$REG" "initialize_verifiers(address,address)" "$GKR" "$WHIR" \
  --private-key "$KEY" --rpc-url "$RPC" >/dev/null

echo "== real per-transaction gas (anvil, Prague / EIP-7623) =="
run() {
  name=$1; addr=$2; file=$3
  counts=$(python3 - "$file" <<'PYCOUNTS'
import pathlib, sys
calldata = bytes.fromhex(pathlib.Path(sys.argv[1]).read_text())
print(len(calldata), calldata.count(0))
PYCOUNTS
)
  bytes=${counts% *}; zeros=${counts#* }
  # WHIR hex exceeds Linux's per-argument limit. Send from stdin through the
  # task-owned anvil's unlocked account; all proof bytes remain tx calldata.
  response=$(python3 - "$file" "$initializer" "$addr" <<'PYRPC' | curl --fail --silent --show-error -H 'Content-Type: application/json' --data-binary @- "$RPC"
import json, pathlib, sys
calldata = bytes.fromhex(pathlib.Path(sys.argv[1]).read_text())
print(json.dumps({"jsonrpc": "2.0", "id": 1, "method": "eth_sendTransaction",
    "params": [{"from": sys.argv[2], "to": sys.argv[3], "gas": "0x17d7840",
        "data": "0x" + calldata.hex()}]}))
PYRPC
)
  tx=$(printf '%s' "$response" | jq -er '.result') || {
    printf '%s\n' "$response" >&2; exit 1;
  }
  receipt=$(cast receipt "$tx" --rpc-url "$RPC" --json)
  used=$(printf '%s' "$receipt" | jq -r '.gasUsed')
  status=$(printf '%s' "$receipt" | jq -r '.status')
  printf "  %-4s : gasUsed = %d  (status %s, calldata %d bytes, zero bytes %d)\n" "$name" "$used" "$status" "$bytes" "$zeros"
  case "$status" in 0x1|1) ;; *) echo "$name transaction failed" >&2; exit 1 ;; esac
}
run GKR "$GKR" "$DATA_ROOT/gkr_full_calldata.hex"
run WHIR "$WHIR" "$DATA_ROOT/proth120_whir_calldata_from_proof.hex"
