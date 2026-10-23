import Human.RV32
import Human.SpecMerkle

/-! # Runs of delegation calls (statements only)

`Delegations.lean` says what one call does. A call is a piece of an operation and means something only inside a run
of calls with the layout and control word the run expects (its ABI); calls used any other way (another control word,
overlapping buffers, a run cut short or mixed with other code) are undefined behaviour: the spec still says what each
such call does, or that it has no next state, and nothing more is claimed. These are the runs and what they compute:
* 7 Blake2s round calls: the (7-round) Blake2s compression function, or in compression mode the two-to-one hash
  `hash2`; 10 calls in the 10-round schedule: RFC 7693's compression `compressRounds 10`, in either mode;
* 56 Blake2s `G` calls: 7 Blake2s rounds; 80 calls: 10 rounds;
* 649 Keccak special5 calls, and 361 calls of the three Keccak-f1600 circuits: Keccak-f[1600].
`CallsRun`: `calls` is what the machine's `run` does on consecutive `csrrw` delegation words in ROM. bigint has no runs: one call is the whole
256-bit operation (`bigintOp`). The proofs are in `slop/Slop/Deleg/`; `verify.sh` checks that they prove exactly
these statements. -/

namespace RV
open Spec

/-- The delegation calls `ks`, one after another from `s`: each call's effect applied. -/
def calls : List DelegationKind → State → Option State
  | [], s => some s
  | k :: ks, s => ((Delegation.effect k (s.getReg 10) (s.getReg 11) (s.getReg 12) s.mem).bind s.applyEffect).bind
      (calls ks)

/-- Delegation instructions of the kinds `ks`, in ROM from the pc, run as the calls `ks`. -/
def CallsRun : Prop :=
  ∀ (ks : List DelegationKind) (s t : State), s.pc.toNat % 4 = 0 → s.pc.toNat + 4 * ks.length ≤ ROM_END →
    (∀ i (h : i < ks.length), decode (read s.mem (s.pc + BitVec.ofNat 32 (4 * i)) 4) = some (.delegate ks[i])) →
    calls ks s = some t → run ks.length s = some t

/-- `n` bytes at `a`, `al`-aligned, in RAM. -/
def Buffer (a : Word) (n al : Nat) : Prop := ROM_END ≤ a.toNat ∧ a.toNat % al = 0 ∧ a.toNat + n ≤ RAM_END

/-- `[a, a + n)` and `[b, b + m)` do not overlap. -/
def Apart (a : Word) (n : Nat) (b : Word) (m : Nat) : Prop := a.toNat + n ≤ b.toNat ∨ b.toNat + m ≤ a.toNat

/-- From `s` to `s'` only the bytes `[a, a + n)` and register `r` changed. -/
def ChangesOnly (s s' : State) (a : Word) (n : Nat) (r : Reg) : Prop :=
  (∀ b : Word, b.toNat < a.toNat ∨ a.toNat + n ≤ b.toNat → s'.mem b = s.mem b) ∧ ∀ i, i ≠ r → s'.getReg i = s.getReg i

/-- Blake2s compression: 7 round calls (CSR `0x7c7`) from `x12 = 0x90000` (7 rounds, round 0). At `x10 = p` the
state `h` (8 words), then the work vector (16 words; words 12 and 14 hold the counter `t` and the last-block flag
as Blake2s mixes them in); the block `m` at `x11 = q`. The state becomes `compress h m t last`. -/
def BlakeCompressRun : Prop :=
  ∀ (s : State) (p q t : Word) (last : Bool), Buffer p 96 128 → Buffer q 64 64 → Apart p 96 q 64 →
    s.getReg 10 = p → s.getReg 11 = q → s.getReg 12 = 0x90000#32 →
    (readWords s.mem (p + 32) 16)[12] = t ^^^ IV 4 →
    (readWords s.mem (p + 32) 16)[14] = (if last then 0xFFFFFFFF#32 else 0#32) ^^^ IV 6 →
    ∃ s', calls (.replicate 7 .blakeRound) s = some s' ∧ ChangesOnly s s' p 96 12 ∧
      readWords s'.mem p 8 = compress (readWords s.mem p 8) (readWords s.mem q 16) t last

/-- The two-to-one hash: 7 round calls in compression mode, `x12 = 0xd0000` (the node `h` at `x10 = p` is the left
input) or `0xf0000` (the right one), the sibling `n` in the first 8 words at `x11 = q`. The words at `p` become
`hash2 h n` (or `hash2 n h`). -/
def BlakeHashRun : Prop :=
  ∀ (s : State) (p q : Word) (right : Bool), Buffer p 96 128 → Buffer q 64 64 → Apart p 96 q 64 →
    s.getReg 10 = p → s.getReg 11 = q → s.getReg 12 = (if right then 0xf0000#32 else 0xd0000#32) →
    ∃ s', calls (.replicate 7 .blakeRound) s = some s' ∧ ChangesOnly s s' p 96 12 ∧
      readWords s'.mem p 8 =
        if right then hash2 (readWords s.mem q 8) (readWords s.mem p 8) else hash2 (readWords s.mem p 8) (readWords s.mem q 8)

/-- Blake2s compression, 10 rounds (RFC 7693): 10 round calls from `x12 = 0x80000` (10 rounds, round 0), layout as
for 7. -/
def BlakeCompressRun10 : Prop :=
  ∀ (s : State) (p q t : Word) (last : Bool), Buffer p 96 128 → Buffer q 64 64 → Apart p 96 q 64 →
    s.getReg 10 = p → s.getReg 11 = q → s.getReg 12 = 0x80000#32 →
    (readWords s.mem (p + 32) 16)[12] = t ^^^ IV 4 →
    (readWords s.mem (p + 32) 16)[14] = (if last then 0xFFFFFFFF#32 else 0#32) ^^^ IV 6 →
    ∃ s', calls (.replicate 10 .blakeRound) s = some s' ∧ ChangesOnly s s' p 96 12 ∧
      readWords s'.mem p 8 = compressRounds 10 (readWords s.mem p 8) (readWords s.mem q 16) t last

/-- The two-to-one hash with 10 rounds: 10 round calls from `x12 = 0xc0000` (left) or `0xe0000` (right). -/
def BlakeHashRun10 : Prop :=
  ∀ (s : State) (p q : Word) (right : Bool), Buffer p 96 128 → Buffer q 64 64 → Apart p 96 q 64 →
    s.getReg 10 = p → s.getReg 11 = q → s.getReg 12 = (if right then 0xe0000#32 else 0xc0000#32) →
    ∃ s', calls (.replicate 10 .blakeRound) s = some s' ∧ ChangesOnly s s' p 96 12 ∧
      readWords s'.mem p 8 = compressRounds 10 (Vector.ofFn configuredIV)
        (if right then readWords s.mem q 8 ++ readWords s.mem p 8 else readWords s.mem p 8 ++ readWords s.mem q 8)
        64#32 true

/-- Keccak-f[1600]: 649 special5 calls (CSR `0x7cb`) from `x10 = 0` on the 25 lanes at `x11 = p` (6 scratch lanes
after them). -/
def KeccakSpecial5Run : Prop :=
  ∀ (s : State) (p : Word), Buffer p 248 256 → s.getReg 10 = 0 → s.getReg 11 = p →
    ∃ s', calls (.replicate 649 .keccak) s = some s' ∧ ChangesOnly s s' p 248 10 ∧
      readLanes s'.mem p 25 = keccakF (readLanes s.mem p 25)

/-- The order of the Keccak-f1600 calls: per round 5 column parity, 5 θ+ρ, 5 χ calls; then one column parity. -/
def f1600Calls : List DelegationKind :=
  (List.replicate 24 (.replicate 5 .keccakParity ++ .replicate 5 .keccakThetaRho ++ .replicate 5 .keccakChi5)).flatten ++
    [.keccakParity]

/-- Keccak-f[1600] in the three circuits (CSRs `0x7cc` … `0x7ce`): 361 calls from `x10 = 0`, as for special5. -/
def KeccakF1600Run : Prop :=
  ∀ (s : State) (p : Word), Buffer p 248 256 → s.getReg 10 = 0 → s.getReg 11 = p →
    ∃ s', calls f1600Calls s = some s' ∧ ChangesOnly s s' p 248 10 ∧
      readLanes s'.mem p 25 = keccakF (readLanes s.mem p 25)

end RV
