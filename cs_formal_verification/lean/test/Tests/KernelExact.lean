module
import Proven.KernelExact

namespace Tests.KernelExact

example : True := by kernel_exact True.intro

/--
error: (kernel) declaration type mismatch, 'Tests.KernelExact.rejected' has type
  True
but it is expected to have type
  False
-/
#guard_msgs in
public theorem rejected : False := by kernel_exact True.intro

end Tests.KernelExact
