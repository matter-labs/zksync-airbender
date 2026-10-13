# Unified-machine shared context

This directory defines shared context for the unified machine artifact, including
its public program, native layout and joint histories with all worker families. It
states fetch/request matching and the input contracts for mixed memory,
native-clock windows and control preparation. These are the inputs and
interpretations used by execution claims, rather than whole-execution conclusions.

[Registry](Registry.lean) connects the machine row to its imported layout.
[Program](Program.lean), [ExecutionInputs](ExecutionInputs.lean) and
[CustomInputs](CustomInputs.lean) name the public decoder/initialization/profile inputs.
[NativeROM](NativeROM.lean) exposes the ordinary-machine ROM view.

[RequestTrace](RequestTrace.lean) and [WorkerProjection](WorkerProjection.lean)
connect full caller requests to workers. [MixedMemory](MixedMemory.lean) retains
machine ports and all worker families in the same history; [MixedFetch](MixedFetch.lean)
binds current-state fetch.

[Windows](Windows.lean), [WindowProjection](WindowProjection.lean) and
[WindowSchedule](WindowSchedule.lean) describe native-clock cuts and selected regions.
[ControlPreparation](ControlPreparation.lean) names the public preparation registry.
Boundary timestamps are retained; scheduling, actual controls and intermediate
states are derived rather than supplied.

The native domain, public program, protocol counts and existing prefix scope
remain explicit. These helpers do not claim whole mixed caller retirement.
Follow [unified trace review](../../Trace/UnifiedReduced/README.md) for actual conclusions.
