import Airbender.Proofs.ReducedMachine.NativePointerPrefix

namespace Airbender.NativePointerPrefix
/-- Actual active pointer-prefix BODY and nonpadding RAM initialization on the
    complete ordinary row domain. Worker BODY, memory auxiliaries, fetched code,
    global statements and physical refinement remain separate obligations. -/
theorem native_pointer_initialization_prefix :
    ∃ activeRows idle, Components activeRows idle :=
  NativePointerPrefixProofs.fixture
end Airbender.NativePointerPrefix
