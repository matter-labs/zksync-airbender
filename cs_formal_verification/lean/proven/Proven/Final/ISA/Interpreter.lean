import Proven.ISA.Sail.InterpreterWitness

namespace Airbender

theorem run_sail_simulation : RunSailSimulationClaim := @Proven.Interpreter.transport

theorem run_sail_simulation_satisfiable : RunSailSimulationSatisfiableClaim :=
  Proven.Interpreter.run_sail_simulation_satisfiable

theorem machine_run_is_sequential : MachineRunIsSequentialClaim := Proven.Interpreter.machine_run_is_sequential

theorem machine_run_is_sequential_satisfiable : MachineRunIsSequentialSatisfiableClaim :=
  Proven.Interpreter.machine_run_is_sequential_satisfiable

end Airbender
