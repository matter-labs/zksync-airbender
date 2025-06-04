#!/bin/sh
#
#   This script runs two processes:
#   1)  anvil-zksync on port 8011  (runs in background)
#   2)  zksync-airbender on port 3030 (runs in foreground)
#

# BUILD_NUMBER is here to prevent asking for telemetry.

# Start anvil-zksync in the background, listening on port 8011
exec /app/anvil-zksync --port 8011 --use-boojum --boojum-bin-path /app/app.bin &
ANVIL_PID=$!

# Give it a moment to bind the port (optional; remove if you prefer)
sleep 1

# Then start zksync-airbender in the foreground on port 3030
exec /app/zksmith --host-port 0.0.0.0:3030 --anvil-url http://localhost:8011 --zksync-os-bin-path /app/app.bin