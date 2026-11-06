import Airbender.Review.Circuits.ReducedMachine.ShiftWrite

namespace Airbender.ReducedMachine.NativePortProofs
open Native
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

theorem source_columns : (importedConstraintsMemoryPorts[0]'(by decide)).readValue =
    Trace.WordColumns.u16 #v[35,36] := rfl

theorem address_columns : rdPort.address = Trace.MemoryAddress.mixed 89 true #v[45,46] := rfl

theorem write_columns : rdPort.writeValue = some (Trace.WordColumns.u16 #v[43,44]) := rfl

theorem decoder_columns : importedConstraintsDecoderColumns =
    (⟨5,6,7,8,#v[9,10],11,12⟩ : Trace.DecoderColumns) := rfl

theorem final_pc_columns : importedConstraintsTraceColumns.finalPC = #v[13,14] := rfl

end Airbender.ReducedMachine.NativePortProofs
