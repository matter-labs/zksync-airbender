#!/usr/bin/env python3
"""Assemble the twelve actual compiler-row bridges into pooled execution."""
from pathlib import Path
from export_gkr_translations import LEAN
from gkr_pooled_row_instances import CASES


def module():
    cases=[stem+mode for stem,_ in CASES for mode in ['Uncached','Cached']]
    text=''.join('import GKRProtocol.PooledRowNative.'+case+'\n' for case in cases)
    text+='''import GKRProtocol.PublicProgram
import Airbender.Proofs.Tables.DecoderPCLow
import Airbender.Proofs.Trace.PooledOracleComposition

namespace Airbender.Compiler.PooledExecution
open Airbender Airbender.Compiler Airbender.Trace Reference.RiscV.Sail
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Each physical row retains its actual family and cache-mode proof. -/
inductive RowCertificate where
'''
    for case in cases:text+='  | '+case[0].lower()+case[1:]+' (cert : PooledRowNative.'+case+'.Certificate)\n'
    text+='\ndef RowCertificate.row : RowCertificate → Row babyBearModulus PooledFamily\n'
    for case in cases:text+='  | .'+case[0].lower()+case[1:]+' cert => PooledRowNative.'+case+'.row cert\n'
    text+='''
theorem row_active (cert : RowCertificate) :
    cert.row.assignment cert.row.columns.execute = 1 := by
  cases cert with
'''
    for case in cases:text+='  | '+case[0].lower()+case[1:]+' cert => exact PooledRowNative.'+case+'.active cert\n'
    text+='''
theorem row_constraints (cert : RowCertificate) {before : Reference.RiscV.Sail.State}
    (image : ROM.ImportedImage before) {cells : List Cell}
    {tokens : List (MemoryToken babyBearModulus)}
    (physical : initialImage before cells = some tokens)
    (domain : ROMNative.WordFullPublic.CoversROM cells) :
    FlatOperation.ConstraintsHoldFlat (Verification.environment cert.row.assignment)
      (cert.row.constraints (⟨ROM.table cells tokens,
        Verification.subwordTable (ROM.words before)⟩ : PooledSetup babyBearModulus)) := by
  cases cert with
'''
    for case in cases:text+='  | '+case[0].lower()+case[1:]+' cert => exact PooledRowNative.'+case+'.constraints cert image physical domain\n'
    text+='''
theorem row_decoded (cert : RowCertificate)
    (typed : cert.row.decoderQuery[0].val < 65536) :
    (decoderTable NativeDecoder.pooledProgram cert.row.family).Contains #[]
      cert.row.decoderQuery := by
  cases cert with
'''
    for case in cases:text+='  | '+case[0].lower()+case[1:]+' cert => exact PooledRowNative.'+case+'.decoded cert typed\n'
    text+='''
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- Public starting state, domain and verifier boundary. No per-row result,
constraint validity or decoder membership is assumed by these fields. -/
structure PublicBoundary (trace : PooledTrace babyBearModulus)
    (before : Reference.RiscV.Sail.State) (cells : List Cell) : Prop where
  image : ROM.ImportedImage before
  domain : ROMNative.WordFullPublic.CoversROM cells
  registers : ∀ index, Cell.register index ∈ cells
  ordinary : ∀ address, Cell.ram address ∈ cells → PlatformWordAddress address
  configuration : FlatMemoryConfiguration before
  landingPadDisabled : ∃ security, before.regs.get? .mseccfg = some security ∧
    SailRV32.Functions._get_Seccfg_MLPE security = 0
  distinct : cells.Nodup
  aligned : ∀ cell ∈ cells, cell.Aligned
  profile : InitialProfile before cells
  seed : trace.initialMemory = ROMView.nativeBootImage cells
  initialBoundary : trace.initial = PCState.boundary 0 (4, 0)
  physicalImage : ∃ tokens, initialImage before cells = some tokens ∧
    trace.rom.wordMemory = ROM.table cells tokens
  subwordSetup : trace.rom.subwordMemory = Verification.subwordTable (ROM.words before)
  verifierBoundary : VerifierBoundary.BootClosure trace.initial
    (trace.rows.map Row.start) (trace.rows.map Row.finish)

theorem boot_inputs {trace : PooledTrace babyBearModulus}
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (boundary : PublicBoundary trace before cells) :
    PooledBootInputs trace before cells NativeDecoder.pooledProgram NonDeterminism.Pooled.decoderFields := by
  exact {
    registers := boundary.registers
    ordinary := boundary.ordinary
    configuration := boundary.configuration
    landingPadDisabled := boundary.landingPadDisabled
    code := PublicProgram.pooled_code
    loads := PublicProgram.pooled_loads
    distinct := boundary.distinct
    aligned := boundary.aligned
    programImage := ⟨_, PublicProgram.pooled_external_image boundary.image⟩
    profile := boundary.profile
    seed := boundary.seed
    initialBoundary := boundary.initialBoundary
    physicalImage := boundary.physicalImage
    subwordSetup := boundary.subwordSetup
    verifierBoundary := boundary.verifierBoundary }

/-- Native equations and source-frame lookup validity construct acceptance.
Exact state and RAM matching remain logical argument-boundary premises. -/
theorem accepted {trace : PooledTrace babyBearModulus}
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (boundary : PublicBoundary trace before cells) (certificates : List RowCertificate)
    (rowBinding : trace.rows = certificates.map RowCertificate.row)
    (states : (trace.initial :: trace.rows.map Row.finish).Perm
      (trace.terminal :: trace.rows.map Row.start))
    (memory : (trace.initialMemory ++ trace.rows.flatMap Row.writes).Perm
      (trace.terminalMemory ++ trace.rows.flatMap Row.reads)) : Accepted trace := by
  obtain ⟨tokens, image, wordSetup⟩ := boundary.physicalImage
  have setup : trace.rom = (⟨ROM.table cells tokens,
      Verification.subwordTable (ROM.words before)⟩ : PooledSetup babyBearModulus) := by
    cases actual : trace.rom with
    | mk word subword =>
      have left := wordSetup
      have right := boundary.subwordSetup
      rw [actual] at left right
      cases left
      cases right
      rfl
  refine ⟨?_, ?_, states, memory⟩
  · intro row member
    rw [rowBinding] at member
    obtain ⟨cert, _, rfl⟩ := List.mem_map.mp member
    rw [setup]
    exact row_constraints cert boundary.image image boundary.domain
  · intro row member
    rw [rowBinding] at member
    obtain ⟨cert, _, rfl⟩ := List.mem_map.mp member
    exact row_active cert

omit [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception] in
theorem decoded {trace : PooledTrace babyBearModulus}
    (certificates : List RowCertificate) (rowBinding : trace.rows = certificates.map RowCertificate.row)
    (native : Accepted trace) (initial : trace.initial.word.lo < Arithmetic.limbBase) :
    PooledDecoded trace NativeDecoder.pooledProgram := by
  have typed := NativeDecoder.Proofs.pooled_query_pc_low (by decide +kernel) native initial
  intro row member
  have range := typed row member
  rw [rowBinding] at member
  obtain ⟨cert, _, rfl⟩ := List.mem_map.mp member
  exact row_decoded cert range

/-- Compiler-to-Sail composition for the retained pooled compiler captures.
Constraints and decoding are conclusions. Public configuration, logical matching,
serialized inverses and commitment authentication remain separate boundaries. -/
theorem native_execution {trace : PooledTrace babyBearModulus}
    {before : Reference.RiscV.Sail.State} {cells : List Cell}
    (boundary : PublicBoundary trace before cells) (certificates : List RowCertificate)
    (rowBinding : trace.rows = certificates.map RowCertificate.row)
    (states : (trace.initial :: trace.rows.map Row.finish).Perm
      (trace.terminal :: trace.rows.map Row.start))
    (memory : (trace.initialMemory ++ trace.rows.flatMap Row.writes).Perm
      (trace.terminalMemory ++ trace.rows.flatMap Row.reads))
    (inverse : SerializedInverse.Clock babyBearModulus)
    {stream : List (BitVec 32)} (ports : NonDeterminism.Pooled.StreamPorts trace stream) :
    NonDeterminism.Pooled.Realizes stream NativeDecoder.pooledProgram trace before cells
      (ROMView.token before) := by
  have native := accepted boundary certificates rowBinding states memory
  have initial : trace.initial.word.lo < Arithmetic.limbBase := by
    rw [boundary.initialBoundary]
    decide +kernel
  exact NonDeterminism.Pooled.Proofs.native_trace_execution (by decide +kernel) inverse
    (boot_inputs boundary) native (decoded certificates rowBinding native initial) ports

end Airbender.Compiler.PooledExecution
'''
    return text

if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true')
    parser.add_argument('--write',action='store_true')
    args=parser.parse_args();path=LEAN/'GKRProtocol/PooledExecution.lean';text=module()
    if args.check and (not path.exists() or path.read_text()!=text):raise ValueError('pooled execution assembly changed')
    if args.write and (not path.exists() or path.read_text()!=text):path.write_text(text)
