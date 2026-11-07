#!/usr/bin/env python3
"""Guard the reviewed Rust public-window interpretation against source drift."""
import hashlib
import json
from export_gkr_translations import LEAN, ROOT

SOURCES = {
    'prover/src/gkr/prover/forward_loop/mod.rs',
    'prover/src/gkr/prover/forward_loop/utils.rs',
    'prover/src/gkr/virtual_polys/init_and_teardown_base.rs',
    'prover/src/gkr/prover/mod.rs',
}


def main():
    manifest=json.loads((LEAN/'artifacts/compiler/interpretation/window-semantics.json').read_text())
    if manifest['format_version'] != 1 or set(manifest['sources']) != SOURCES:
        raise ValueError('window-semantics source inventory changed')
    for path,record in manifest['sources'].items():
        if hashlib.sha256((ROOT/path).read_bytes()).hexdigest()!=record['sha256']:
            raise ValueError('native window semantics changed; review before repinning: '+path)
        if not record['observation'] or not record['inspected_spans']:
            raise ValueError('missing native interpretation evidence: '+path)
    print('PASS four reviewed native window-semantics source pins; Rust interpretation boundary remains explicit')


if __name__=='__main__':main()
