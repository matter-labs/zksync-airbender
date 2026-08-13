#!/usr/bin/env bash
# Device IDENTITY and STATE, in one place, for every session driver and capture helper this benchmark
# has or will have.
#
# WHY THIS FILE EXISTS. Up to v3 R9 every archived telemetry sidecar in this campaign recorded device
# STATE — clocks, power, temperature, throttle reasons — and never device IDENTITY. So none of the
# anchor reference literals those rungs froze can be shown to have come from a particular GPU, and
# when four of them ended up disagreeing by 2.8 % on one lane there was no way to tell a machine
# change from a composition change. R9b closed the gap by querying identity beside state, RR re-based
# the campaign's references on that session, and the identity is now a REQUIRED field of the
# reference (`R9B_BASELINE_DEVICE` in `tools/r4_table.py`).
#
# SO: a future rung's session driver, soak mark, G0 driver or capture helper takes its telemetry from
# HERE rather than writing its own `nvidia-smi` line. `state` alone is never enough — `sidecar` is the
# call that cannot forget identity, and `r7_gates.sh`'s `identity` lane gates the query itself and
# compares the live uuid against the committed baseline's.
#
#   gpu_identity.sh identity   one `;`-joined row: index,name,uuid,serial,driver,vbios,pstate,
#                              clocks.max.sm,clocks.sm,power.limit,power.draw,temperature,
#                              utilization,mig.mode,compute_mode
#   gpu_identity.sh header     that query's CSV header, so a sidecar is self-describing
#   gpu_identity.sh field <n>  one named field of the identity row (uuid, serial, driver_version, …)
#   gpu_identity.sh state      the volatile subset a soak mark wants, `;`-joined
#   gpu_identity.sh apps       resident compute processes, `;`-joined, empty when the GPU is idle
#   gpu_identity.sh sidecar [label]   identity + state + apps as a labelled block — THE call a
#                              session driver should make before and after every measured phase
set -uo pipefail

IDENT_Q='index,name,uuid,serial,driver_version,vbios_version,pstate,clocks.max.sm,clocks.sm,power.limit,power.draw,temperature.gpu,utilization.gpu,mig.mode.current,compute_mode'
STATE_Q='clocks.sm,clocks.mem,power.draw,clocks_event_reasons.active,temperature.gpu,utilization.gpu'

smi() { nvidia-smi --query-gpu="$1" --format=csv,noheader | tr -s ' ' | paste -sd';' -; }

case "${1:-identity}" in
  identity) smi "$IDENT_Q" ;;
  header)   nvidia-smi --query-gpu="$IDENT_Q" --format=csv | head -1 ;;
  state)    smi "$STATE_Q" ;;
  apps)     nvidia-smi --query-compute-apps=pid,process_name,used_memory --format=csv,noheader \
              | tr -s ' ' | paste -sd';' - ;;
  field)
    [ $# -ge 2 ] || { echo "usage: $0 field <query-field>" >&2; exit 2; }
    nvidia-smi --query-gpu="$2" --format=csv,noheader | head -1 | sed 's/^ *//; s/ *$//' ;;
  sidecar)
    printf 'gpu-sidecar %s\n' "${2:-unlabelled}"
    printf '  identity-header %s\n' "$(nvidia-smi --query-gpu="$IDENT_Q" --format=csv | head -1)"
    printf '  identity        %s\n' "$(smi "$IDENT_Q")"
    printf '  state           %s\n' "$(smi "$STATE_Q")"
    printf '  compute-apps    %s\n' "$(nvidia-smi --query-compute-apps=pid,process_name,used_memory \
                                        --format=csv,noheader | tr -s ' ' | paste -sd';' -)"
    printf '  ncu             %s\n' "$(ncu --version 2>/dev/null | sed -n 's/^Version //p' | head -1)"
    printf '  cuda            %s\n' "$(nvcc --version 2>/dev/null | sed -n 's/.*release //p' | head -1)"
    ;;
  *) echo "usage: $0 {identity|header|field <name>|state|apps|sidecar [label]}" >&2; exit 2 ;;
esac
