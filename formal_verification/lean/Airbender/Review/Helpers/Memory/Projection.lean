import Airbender.Review.Helpers.Memory.SailHistory

namespace Airbender.Trace

/-- Retain complete address domains in an existing Clean history. Native
    acceptance still checks the original, unfiltered history and all its clocks. -/
def projectHistory (keep : Nat → Bool) (history : TimestampSortedMemoryAccessList) :
    TimestampSortedMemoryAccessList :=
  ⟨history.val.filter (fun event => keep event.2.1), history.property.filter _⟩

end Airbender.Trace
