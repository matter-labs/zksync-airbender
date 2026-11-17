# Native setup inputs

Each family module imports one native setup JSON as data (`import_setup_blocks`). The
[content pins](../../../../setup_json_pins.json) cover every setup input. Lake tracks the JSON inputs and rebuilds
dependent modules on a change. Start with [AddSub.lean](AddSub.lean).

Kernel claims make the table definitions equal to the imported rows: `SetupImportClaim` in the SetupImport module
next to the bigint, G and Keccak tables, the `…ImportClaim` statements of [Claims.lean](Claims.lean) for the CPU
fixed regions and the shift/byte rows, `Range13ImportClaim` and `CPURangesImportClaim` in [Ranges.lean](Ranges.lean),
and `NativeWorkerSetup.SetupImportClaim` ([WorkerSetupImport.lean](../WorkerSetupImport.lean)) for the public worker
tables with their range columns. Only these claim modules import the data modules; the table definitions do not.
[NativePublicSetup.lean](../NativePublicSetup.lean) defines the public rows used by the machine claims. See the
[compiler guide](../README.md) for their interfaces.
