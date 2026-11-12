# Compiler proof source

The templates retain the complete generator inputs of the frozen compiler port.
The exporter checks every declaration and records its explicit Lean source.
The batch generator retains all declarations, including manual definitions and the checked expansion of each metadata command.
It factors closed expression trees and long literal lists. It then uses actual declaration dependencies to form small modules.
Each aggregate module imports every part without a condition. The kernel checks all generated source.

Run the commands from the Lean directory. Build the small importers first.
Export and split the foundation templates, then build their aggregate modules.
Next export and split the numeric data and trace templates, and build their certificate dependencies.
Last, export and split the clean arithmetic templates.
Pass a template name from `manifest.json` to each command:

```sh
python3 scripts/compiler_batches.py export FullArithmeticNative-BigintCachedFoundation
python3 scripts/compiler_batches.py split FullArithmeticNative-BigintCachedFoundation
```

The export logs and temporary source are in `.lake/compiler-exports/`.
The formal build enforces the same fixed module CPU limit on every generated part.
Large conversion proofs use the existing `kernel_rfl` tactic. It leaves the complete equality check to the kernel.

`python3 scripts/compiler_native_bindings.py` emits every native gate and placement binding.
Each aggregate retains every batch. The kernel checks the raw relation and address equalities.
