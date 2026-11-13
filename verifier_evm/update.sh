#!/usr/bin/env bash
set -euo pipefail

echo "Updating foundryup + forge..."
foundryup --update
foundryup
forge --version

echo
echo "Updating solc-select + solc..."
python3 -m pip install --user --break-system-packages --upgrade solc-select
solc-select install latest
solc-select use "$(solc-select versions | awk '{ print $1 }' | sort -V | tail -1)"
solc --version

echo
echo "Updating solx..."
latest_url="$(curl -fsSL -o /dev/null -w '%{url_effective}' https://github.com/NomicFoundation/solx/releases/latest)"
latest="${latest_url##*/}"
current="$(solx --version | sed -n 's/^solx v\([^,]*\),.*/\1/p')"

if [ "$current" != "$latest" ]; then
    curl -fL \
        "https://github.com/NomicFoundation/solx/releases/download/$latest/solx-linux-amd64-gnu-v$latest" \
        -o "$(command -v solx)"
    chmod +x "$(command -v solx)"
fi

solx --version
