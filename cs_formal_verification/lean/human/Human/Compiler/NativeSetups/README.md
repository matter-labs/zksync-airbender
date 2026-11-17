# Native setup inputs

Each family module imports one native setup JSON as data (`import_setup_blocks`). The
[content pins](../../../../setup_json_pins.json) cover every setup input. Lake tracks the JSON inputs and rebuilds
dependent modules on a change. Start with [AddSub.lean](AddSub.lean).

Kernel claims make the table definitions equal to the imported rows: `SetupImportClaim` next to the bigint, G and
Keccak tables, `ShiftBinopImportClaim` in [Bytes.lean](../../Helpers/Tables/Bytes.lean), the `…ImportClaim`
statements of [NativeFixedRows.lean](../NativeFixedRows.lean), `Range13ImportClaim` in [Ranges.lean](Ranges.lean),
and `NativeWorkerSetup.SetupImportClaim` for the public worker tables with their range columns.
[NativePublicSetup.lean](../NativePublicSetup.lean) defines the public rows used by the machine claims. See the
[compiler guide](../README.md) for their interfaces.
