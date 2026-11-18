#!/usr/bin/env python3
"""Emit independent kernel checks for native worker selector batches and groups.

The kernel follows each worker's native lookup chains once (Chains.lean). Each batch module resolves its selectors and
reads their groups from these chains. Usage: generate_worker_selector_proofs.py [--check]; --check compares the
committed modules with the output."""
import argparse
import json
import sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from generate_worker_selectors import native_chains, FAMILIES, WORKERS

VARIANTS = {'Bigint': 'bigint', 'BlakeG': 'blakeG', 'BlakeRound': 'blakeRound', 'KeccakColumnParity': 'columnParity',
            'KeccakThetaRho': 'thetaRho', 'KeccakChi5': 'chi5'}
BATCH = 16


def header(title, imports):
    return ('module\n' + ''.join(f'public import {module}\n' for module in imports) + f'''
@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeWorkerLookups.Proofs.{title}
set_option maxRecDepth 32768
''')


def footer(title):
    return f'\nend Airbender.Compiler.NativeWorkerLookups.Proofs.{title}\n'


def family_modules(title, variant, entries, chains):
    """The generated modules of one worker, as {path relative to WorkerSelectors: text}."""
    prefix = f'Proven.Compiler.WorkerSelectors.{title}'
    count = (len(entries) + BATCH - 1) // BATCH
    batches = [f'batch{index:03d}' for index in range(count)]
    listed = '[' + ', '.join(batches) + ']'
    literal = '[' + ', '.join(f'(({gate}, {operand}), {group})' for (gate, operand), group in chains) + ']'
    modules = {f'{title}/Chains.lean': header(title, ['Proven.Compiler.WorkerSelectors.Common']) + f'''
/-- Each operand of a public lookup chain with the group of its output, in output and chain order. -/
def chains : List ((Nat × Nat) × Fin 3) := {literal}

/-- The kernel follows the actual native chains to these operands and groups. -/
theorem chain_groups : NativeLookups.chainGroups (circuitFor .{variant}) = .ok chains := by
  unfold NativeLookups.chainGroups
  rw [compiled_gates_toList]
  kernel_rfl

/-- A selector has the group of the one chain that contains its operand. -/
def grouping (selector : NativeLookups.Selector) : Bool :=
  (chains.filter (fun entry => entry.1 == (selector.gate, selector.operand))).map Prod.snd == [selector.group]
''' + footer(title)}
    for index in range(count):
        first = index * BATCH
        modules[f'{title}/Part{index:03d}.lean'] = header(
            title, [f'{prefix}.Chains', 'Proven.KernelExact']) + f'''
/-- This contiguous batch retains the native query order. -/
def batch{index:03d} : List NativeLookups.Selector :=
  ((selectorsFor .{variant}).drop {first}).take {min(BATCH, len(entries) - first)}

/-- Every cache or copy expansion in this batch succeeds. -/
theorem resolved{index:03d} : batch{index:03d}.all (fun selector =>
    match NativeLookups.select (circuitFor .{variant}) selector with
    | .ok _ => true | .error _ => false) = true := by
  kernel_exact (resolved_all_eq (circuitFor .{variant}) batch{index:03d}).symm.trans
    (show NativeLookups.resolvedAll (circuitFor .{variant}) batch{index:03d} = true from by kernel_rfl)

/-- Every selector in this batch has its actual native output group. -/
theorem grouped{index:03d} : batch{index:03d}.all grouping = true := by kernel_rfl
''' + footer(title)

    def accepted(proof):
        return ('by\n    refine ⟨' + ', '.join(['?_'] * count + ['True.intro']) + '⟩\n'
                + '\n'.join(f'    · kernel_exact {proof}{index:03d}' for index in range(count)))

    parts = [f'{prefix}.Part{index:03d}' for index in range(count)]
    modules[f'{title}/Grouped.lean'] = header(title, ['Proven.Compiler.WorkerSelectors.Assemble'] + parts) + f'''
/-- The contiguous batches cover every native query selector. -/
theorem batches : selectorsFor .{variant} = ({listed}).flatten := by kernel_rfl

/-- Each worker selector belongs to its actual public native output chain. -/
theorem grouped :
    NativeLookups.groupsAgree (circuitFor .{variant}) (selectorsFor .{variant}) = true := by
  have accepted : AllBatches grouping {listed} :=
    {accepted('grouped')}
  rw [groups_agree_of_chains chain_groups]
  kernel_exact (congrArg (fun values : List NativeLookups.Selector => values.all grouping) batches).trans
    (flatten_all grouping {listed} accepted)
''' + footer(title)
    modules[f'{title}.lean'] = header(title, ['Proven.Compiler.WorkerSelectors.Assemble', f'{prefix}.Grouped'] + parts) + f'''
/-- Every worker query has its actual gate, expansion and native chain group. -/
theorem binding :
    NativeLookups.queryLocators (circuitFor .{variant}) =
      .ok ((selectorsFor .{variant}).map (fun selector => (selector.gate, selector.operand))) ∧
    (selectorsFor .{variant}).all (fun selector =>
      match NativeLookups.select (circuitFor .{variant}) selector with
      | .ok _ => true | .error _ => false) = true ∧
    NativeLookups.groupsAgree (circuitFor .{variant}) (selectorsFor .{variant}) = true := by
  refine ⟨?_, ?_, ?_⟩
  · unfold NativeLookups.queryLocators NativeLookups.locators
    rw [compiled_gates_toList]
    kernel_rfl
  · let predicate := fun selector =>
      match NativeLookups.select (circuitFor .{variant}) selector with
      | .ok _ => true | .error _ => false
    have accepted : AllBatches predicate {listed} :=
      {accepted('resolved').replace(chr(10) + '    ', chr(10) + '      ')}
    kernel_exact (congrArg (fun values : List NativeLookups.Selector => values.all predicate) batches).trans
      (flatten_all predicate {listed} accepted)
  · kernel_exact grouped
''' + footer(title)
    return modules


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    directory = ROOT / 'proven/Proven/Compiler/WorkerSelectors'
    stale = []
    for title, family in WORKERS.items():
        circuit = json.loads((ROOT.parent.parent / f'cs/compiled_circuits/{FAMILIES[family]}_layout_gkr.json').read_text())
        entries, chains = native_chains(circuit)
        modules = family_modules(title, VARIANTS[title], entries, chains)
        for relative, text in modules.items():
            path = directory / relative
            if not args.check:
                path.parent.mkdir(exist_ok=True)
                path.write_text(text)
            elif not path.exists() or path.read_text() != text:
                stale.append(relative)
        for extra in sorted((directory / title).glob('*.lean')):
            if f'{title}/{extra.name}' not in modules:
                if args.check:
                    stale.append(f'{title}/{extra.name}')
                else:
                    extra.unlink()
        print(title, (len(entries) + BATCH - 1) // BATCH, 'selector batches,', len(chains), 'chain operands')
    if stale:
        sys.exit('FAIL worker selector proofs differ from scripts/generate_worker_selector_proofs.py: ' + ', '.join(stale))
    if args.check:
        print('PASS worker selector proofs')


if __name__ == '__main__':
    main()
