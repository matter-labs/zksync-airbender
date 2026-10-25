#!/usr/bin/env python3
"""Replay compiler proof stages with ordinary dependencies and one target at a time.

Use --stage (repeatable) or --from-stage inside bounded_fv.py to keep each run
within its budget. For a time checkpoint within a stage, resume with that stage's
family/mode-selecting script. No timestamps, traces or proof caches are rewritten.
"""
import argparse
import os
import subprocess
import sys

from export_gkr_translations import LEAN

STAGES = {
    'arithmetic': [],
    'lookup_pins': [[sys.executable, 'scripts/check_gkr_lookup_certificates.py']],
    'wiring': [[sys.executable, 'scripts/gkr_wiring_instances.py', '--build']],
    'lookup_fields': [[sys.executable, 'scripts/gkr_lookup_instances.py']],
    'cache': [[sys.executable, 'scripts/gkr_consumer_instances.py', '--stage', 'cache']],
    'typing': [[sys.executable, 'scripts/gkr_consumer_instances.py', '--stage', 'typing']],
    'lookup': [[sys.executable, 'scripts/gkr_consumer_instances.py', '--stage', 'lookup']],
    'lookup_source': [[sys.executable, 'scripts/gkr_lookup_source_certificate.py', '--check'],
                      [sys.executable, 'scripts/gkr_consumer_instances.py', '--stage', 'source']],
    'table': [[sys.executable, 'scripts/gkr_table_instances.py', '--check', '--build']],
    'product': [[sys.executable, 'scripts/gkr_product_instances.py', '--check', '--build']],
    'memory': [[sys.executable, 'scripts/gkr_memory_certificate.py', '--check', '--build']],
    'helper': [[sys.executable, 'scripts/gkr_helper_instances.py', '--check', '--build']],
    'full_arithmetic': [[sys.executable, 'scripts/gkr_full_arithmetic_certificate.py', '--check', '--build']],
    'functional': [[sys.executable, 'scripts/gkr_functional_instances.py', '--check', '--build']],
    'source_links': [[sys.executable, 'scripts/gkr_functional_links.py', '--check', '--build']],
    'source_contracts': [[sys.executable, 'scripts/gkr_source_contract_instances.py', '--check', '--build']],
    'history_erasure': [[sys.executable, 'scripts/gkr_history_erasure_instances.py', '--check', '--build']],
    'helper_validity': [[sys.executable, 'scripts/gkr_helper_validity_instances.py', '--check', '--build']],
    'clean_arithmetic': [[sys.executable, 'scripts/gkr_clean_arithmetic.py', '--check', '--build']],
    'clean_links': [[sys.executable, 'scripts/gkr_clean_links.py', '--check', '--build']],
    'materialized_setup': [[sys.executable, 'scripts/gkr_materialized_setup.py', '--check', '--build']],
    'materialized_tables': [[sys.executable, 'scripts/gkr_materialized_instances.py', '--check', '--build']],
    'counter_frame': [[sys.executable, 'scripts/gkr_counter_frame_instances.py', '--check', '--build']],
    'oracle_frame': [[sys.executable, 'scripts/gkr_oracle_frame_instances.py', '--check', '--build']],
    'query_frame': [[sys.executable, 'scripts/gkr_query_frame_instances.py', '--check', '--build']],
    'materialized_ranges': [[sys.executable, 'scripts/gkr_materialized_range_instances.py', '--check', '--build']],
    'materialized_witness': [[sys.executable, 'scripts/gkr_materialized_witness_instances.py', '--check', '--build']],
    'memory_frames': [[sys.executable, 'scripts/gkr_memory_frame_instances.py', '--check', '--build']],
    'memory_execute': [[sys.executable, 'scripts/gkr_memory_execute_instances.py', '--check', '--build']],
    'framed_witness': [[sys.executable, 'scripts/gkr_framed_witness_instances.py', '--check', '--build']],
    'roots': [],
    'audit': [[sys.executable, 'scripts/audit_gkr_compiler_axioms.py']],
}
TESTS = ['GKRCompiler', 'GKRProtocol', 'Tests.GKRCompilerCertificate', 'Tests.GKRCompilerWiring',
         'Tests.GKRLookupFields', 'Tests.GKRConsumerTypes', 'Tests.GKRCacheBindings',
         'Tests.GKRLookupReduction', 'Tests.GKRBaseEncoding', 'Tests.GKRLookupSource',
         'Tests.GKRSourceTable', 'Tests.GKRNativeProduct', 'Tests.GKRMemorySource',
         'Tests.GKRHelperSources', 'Tests.GKRFullArithmetic', 'Tests.GKRFunctional', 'Tests.GKRHelperValidity',
         'Tests.GKRCleanArithmetic', 'Tests.GKRMaterializedCounters', 'Tests.GKRMemoryFrames']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--stage', choices=STAGES, action='append')
    parser.add_argument('--from-stage', choices=STAGES)
    args = parser.parse_args()
    if args.stage and args.from_stage:
        parser.error('choose --stage or --from-stage')
    stages = list(STAGES)
    if args.stage:
        selected = args.stage
    elif args.from_stage:
        selected = stages[stages.index(args.from_stage):]
    else:
        selected = stages
    environment = dict(os.environ, LEAN_NUM_THREADS='1')

    def run(command):
        subprocess.run(command, cwd=LEAN, env=environment, check=True)

    for stage in selected:
        print('STAGE', stage, flush=True)
        if stage == 'arithmetic':
            for line in (LEAN / 'GKRCompiler.lean').read_text().splitlines():
                if line.startswith('import GKRCompiler.Native.'):
                    run(['lake', '--no-cache', 'build', '+' + line.removeprefix('import ') + ':olean'])
        elif stage == 'roots':
            for target in TESTS:
                run(['lake', '--no-cache', 'build', '+' + target + ':olean'])
        else:
            for command in STAGES[stage]:
                run(command)


if __name__ == '__main__':
    main()
