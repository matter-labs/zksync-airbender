module
import Proven.KernelExact

namespace Tests.KernelExact

example : True := by kernel_exact True.intro

/--
error: (kernel) declaration type mismatch, '_private.Tests.KernelExact.0.Tests.KernelExact._example' has type
  True
but it is expected to have type
  False
-/
#guard_msgs in
example : False := by kernel_exact True.intro

run_meta do
  for (name, info) in (← Lean.getEnv).constants.toList do
    if name.toString.startsWith "_private.Tests.KernelExact." ||
        name.toString.startsWith "Tests.KernelExact." then
      if let .axiomInfo _ := info then
        Lean.throwError "The negative kernel test left an axiom: {name}."

end Tests.KernelExact
