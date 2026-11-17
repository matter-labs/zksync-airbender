import Proven.ISA.Sail.Interpreter

namespace Airbender

theorem run_sail_simulation : RunSailSimulationClaim := Proven.Interpreter.run_sail_simulation

theorem run_sail_simulation_satisfiable : RunSailSimulationSatisfiableClaim :=
  Proven.Interpreter.run_sail_simulation_satisfiable

end Airbender
