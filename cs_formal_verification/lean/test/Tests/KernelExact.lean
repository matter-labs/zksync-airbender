module
import Proven.KernelExact

namespace Tests.KernelExact

example : True := by kernel_exact True.intro

-- Private names depend on the compiler root. Match the kernel error and check the resulting environment.
/-- error: (kernel) declaration type mismatch -/
#guard_msgs (substring := true) in
example : False := by kernel_exact True.intro

run_meta do
  for (name, info) in (← Lean.getEnv).constants.toList do
    if name.toString.startsWith "Tests.KernelExact." ||
        (name.toString.splitOn ".Tests.KernelExact.").length > 1 then
      if let .axiomInfo _ := info then
        Lean.throwError "The negative kernel test left an axiom: {name}."
      if info.type.isConstOf ``False then
        Lean.throwError "The negative kernel test admitted False: {name}."

end Tests.KernelExact
