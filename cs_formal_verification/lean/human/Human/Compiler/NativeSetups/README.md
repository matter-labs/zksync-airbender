# Native setup inputs

The family modules validate each native setup JSON and retain a small content
stamp. The [content pins](../../../../setup_json_pins.json) cover every setup input.
Lake tracks the JSON inputs and rebuilds dependent modules on a change.
Start with [AddSub.lean](AddSub.lean). [Ranges.lean](Ranges.lean) compares the two
range grids with their mathematical definitions.

[NativeGrid.lean](../../Import/NativeGrid.lean) performs these compiled checks.
Its setup row comparisons are the trusted DECISION B binding. The stamps track
inputs; they are not proofs of row equality.
[NativePublicSetup.lean](../NativePublicSetup.lean) defines the public rows used
by the machine claims. See the [compiler guide](../README.md) for their interfaces.
