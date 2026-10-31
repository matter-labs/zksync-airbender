# Public production program differential

The [manifest](zksync-os.json) pins the public ZKsync OS
[v0.5.4 release](https://github.com/matter-labs/zksync-os/releases/tag/v0.5.4-private).
The release tag contains the word `private`. Its binary and text assets are
public downloads. The manifest records the release commit, asset sizes and
published SHA-256 digests. The binary files stay outside this repository.

The [fetch script](../../scripts/fetch_production_program.py) checks each size
and hash before use. It checks cached files too. A changed cached file fails
the check. The script replaces a downloaded file only after verification.

CI compares the compiled Lean decoder rows with native setup exports. It
requires all 14 full and unified comparisons in both cache modes. The
committed verifier programs also cover their reduced setup configurations.
This OS release uses special5, so the reduced preprocessor does not admit it.

These checks establish decoder row equality for this public artifact. They
also check the emitted circuit objects. They do not establish execution under
the three machine targets: those targets exclude special5 calls. Public
supported-use, exact matching and initialization premises remain explicit.
