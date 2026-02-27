# ZKSmith

`zksmith` polls Anvil for ZKsync OS witness data, generates proofs, and serves a local dashboard.

## Run

From workspace root:

```bash
cargo run --release -p zksmith -- \
  --anvil-url http://localhost:8011 \
  --zksync-os-bin-path examples/zksync_os/app.bin
```

Open `http://127.0.0.1:3030`.

## Features

Default features:

- `gpu`
- `security_80`

Run with `security_100`:

```bash
cargo run --release -p zksmith --no-default-features --features gpu,security_100 -- \
  --anvil-url http://localhost:8011 \
  --zksync-os-bin-path examples/zksync_os/app.bin
```

Run without GPU:

```bash
cargo run --release -p zksmith --no-default-features --features security_80 -- \
  --anvil-url http://localhost:8011 \
  --zksync-os-bin-path examples/zksync_os/app.bin
```

## Notes

- `--host-port` overrides the default dashboard bind address (`127.0.0.1:3030`).
- `--output-dir` is accepted by CLI and reserved for output handling extensions.
