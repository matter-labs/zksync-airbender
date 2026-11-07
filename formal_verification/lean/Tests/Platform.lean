import SailRV32

namespace Tests
open _root_.Sail.ArchSem

/-- Explicit upstream device configuration for closed regression fixtures.
The platform's external operations are concrete handlers; no global instance
specializes the polymorphic generated Sail definitions. -/
abbrev upstreamPlatform : MemoryPlatform SailRV32.exception where
  terminalWrite _ := pure ()
  reserve _ _ := pure ()
  reservationMatches _ := false
  devices := DeviceConfiguration.upstream

end Tests
