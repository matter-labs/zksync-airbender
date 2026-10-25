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
    'memory_tokens': [[sys.executable, 'scripts/gkr_memory_ports_instances.py', '--check', '--build']],
    'worker_tokens': [[sys.executable, 'scripts/gkr_worker_ports_instances.py', '--check', '--build']],
    'initialization_tokens': [[sys.executable, 'scripts/gkr_initialization_ports_instances.py', '--check', '--build']],
    'initialization_windows': [[sys.executable, 'scripts/check_gkr_window_semantics.py'],
        [sys.executable, 'scripts/gkr_windowed_instances.py', '--check', '--build'],
        [sys.executable, 'scripts/gkr_windowed_token_instances.py', '--check', '--build'],
        [sys.executable, 'scripts/gkr_windowed_agreement_instances.py', '--check', '--build'],
        [sys.executable, 'scripts/gkr_windowed_witness_instances.py', '--check', '--build'],
        [sys.executable, 'scripts/gkr_windowed_public_instances.py', '--check', '--build']],
    'native_rom': [['lake', '--no-cache', 'build', '+GKRProtocol.ROMNative.WordMemoryPublic:olean'],
                   ['lake', '--no-cache', 'build', '+Tests.GKRNativeROM:olean']],
    'unified_rom': [[sys.executable, 'scripts/gkr_rom_columns.py', '--check', '--build'],
                    [sys.executable, 'scripts/gkr_rom_values.py', '--check'],
                    ['lake', '--no-cache', 'build', '+GKRProtocol.ROMNative.UnifiedPublic:olean'],
                    ['lake', '--no-cache', 'build', '+Tests.GKRUnifiedROM:olean']],
    'subword_public': [[sys.executable, 'scripts/gkr_subword_prefix.py', '--check', '--build'],
                       [sys.executable, 'scripts/gkr_subword_rows.py', '--check'],
                       [sys.executable, 'scripts/gkr_subword_boundary.py', '--check'],
                       ['lake', '--no-cache', 'build', '+GKRProtocol.ROMNative.SubwordPublic:olean'],
                       ['lake', '--no-cache', 'build', '+Tests.GKRSubwordNative:olean']],
    'unified_public': [[sys.executable, 'scripts/check_gkr_unified_scaffolds.py'],
                       ['lake', '--no-cache', 'build', '+GKRProtocol.ROMNative.UnifiedFullPublic:olean'],
                       ['lake', '--no-cache', 'build', '+Tests.GKRBlockSpans:olean'],
                       ['lake', '--no-cache', 'build', '+Tests.GKRUnifiedFullNative:olean']],
    'decoder_arguments': [[sys.executable, 'scripts/gkr_decoder_arguments.py', '--check', '--build'],
                          ['lake', '--no-cache', 'build', '+Tests.GKRDecoderArguments:olean']],
    'decoder_setup': [[sys.executable, 'scripts/check_gkr_decoder_setup_scaffolds.py'],
                      ['lake', '--no-cache', 'build', '+GKRProtocol.DecoderQueryNative.AddSubUncached:olean'],
                      ['lake', '--no-cache', 'build', '+GKRProtocol.DecoderQueryNative.AddSubCached:olean'],
                      ['lake', '--no-cache', 'build', '+GKRProtocol.DecoderQueryNative.JumpBranchUncached:olean'],
                      ['lake', '--no-cache', 'build', '+GKRProtocol.DecoderQueryNative.JumpBranchCached:olean'],
                      ['lake', '--no-cache', 'build', '+GKRProtocol.DecoderQueryNative.MulDivUncached:olean'],
                      ['lake', '--no-cache', 'build', '+GKRProtocol.DecoderQueryNative.MulDivCached:olean'],
                      ['lake', '--no-cache', 'build', '+GKRProtocol.DecoderQueryNative.ShiftBinopUncached:olean'],
                      ['lake', '--no-cache', 'build', '+GKRProtocol.DecoderQueryNative.ShiftBinopCached:olean'],
                      ['lake', '--no-cache', 'build', '+GKRProtocol.DecoderQueryNative.WordMemoryUncached:olean'],
                      ['lake', '--no-cache', 'build', '+GKRProtocol.DecoderQueryNative.WordMemoryCached:olean'],
                      ['lake', '--no-cache', 'build', '+GKRProtocol.DecoderQueryNative.SubwordMemoryUncached:olean'],
                      ['lake', '--no-cache', 'build', '+GKRProtocol.DecoderQueryNative.SubwordMemoryCached:olean'],
                      ['lake', '--no-cache', 'build', '+GKRProtocol.DecoderQueryNative.UnifiedUncached:olean'],
                      ['lake', '--no-cache', 'build', '+GKRProtocol.DecoderQueryNative.UnifiedCached:olean'],
                      ['lake', '--no-cache', 'build', '+Tests.GKRDecoderSetup:olean']],
    'public_execution': [[sys.executable, 'scripts/gkr_pooled_row_instances.py', '--check'],
                         [sys.executable, 'scripts/gkr_pooled_execution.py', '--check'],
                         [sys.executable, 'scripts/gkr_unified_row_instances.py', '--check'],
                         ['lake', '--no-cache', 'build', '+GKRProtocol.PooledExecution:olean'],
                         ['lake', '--no-cache', 'build', '+GKRProtocol.UnifiedExecution:olean']],
    'fixed_setup': [[sys.executable, 'scripts/gkr_fixed_setup_instances.py', '--check', '--build']],
    'clean_fixed_lookup': [[sys.executable, 'scripts/gkr_clean_fixed_instances.py', '--check', '--build']],
    'clean_scalars': [[sys.executable, 'scripts/gkr_clean_scalar_instances.py', '--check', '--build']],
    'clean_arguments': [[sys.executable, 'scripts/gkr_clean_argument_instances.py', '--check', '--build']],
    'clean_generic_arguments': [[sys.executable, 'scripts/gkr_clean_generic_arguments.py', '--check', '--build']],
    'clean_lookup_closure': [[sys.executable, 'scripts/gkr_clean_closed_instances.py', '--check', '--build']],
    'shift_prefix': [[sys.executable, 'scripts/gkr_shift_prefix_instances.py', '--check', '--build'],
                     [sys.executable, 'scripts/gkr_shift_prefix_assembly.py', '--check', '--build']],
    'shift_setup': [['lake', '--no-cache', 'build', '+GKRProtocol.ShiftSetupNative:olean']],
    'clean_shift_lookup': [[sys.executable, 'scripts/gkr_clean_shift_instances.py', '--check', '--build']],
    'clean_trace_witness': [[sys.executable, 'scripts/gkr_clean_witness_instances.py', '--check', '--build']],
    'roots': [],
    'audit': [[sys.executable, 'scripts/audit_gkr_compiler_axioms.py']],
}
TESTS = ['GKRCompiler', 'GKRProtocol', 'Tests.GKRCompilerCertificate', 'Tests.GKRCompilerWiring',
         'Tests.GKRLookupFields', 'Tests.GKRConsumerTypes', 'Tests.GKRCacheBindings',
         'Tests.GKRLookupReduction', 'Tests.GKRBaseEncoding', 'Tests.GKRLookupSource',
         'Tests.GKRSourceTable', 'Tests.GKRNativeProduct', 'Tests.GKRMemorySource',
         'Tests.GKRHelperSources', 'Tests.GKRFullArithmetic', 'Tests.GKRFunctional', 'Tests.GKRHelperValidity',
         'Tests.GKRCleanArithmetic', 'Tests.GKRMaterializedCounters', 'Tests.GKRMemoryFrames',
         'Tests.GKRBlockNormalization', 'Tests.GKRBlockCoverage', 'Tests.GKRShiftSetup', 'Tests.GKRWorkerTokens', 'Tests.GKRInitializationTokens', 'Tests.GKRWindowedInitialization', 'Tests.GKRNativeROM', 'Tests.GKRUnifiedROM', 'Tests.GKRSubwordNative', 'Tests.GKRBlockSpans', 'Tests.GKRUnifiedFullNative', 'Tests.GKRDecoderArguments', 'Tests.GKRDecoderSetup']


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
