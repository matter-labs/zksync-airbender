import Lean
import Human.ISA.RV32
-- simp sets (built once, instead of elaborating lemma lists at every call):
-- rv_word: `decode` of concrete instruction words (generated, slop/Slop/ISA/RV/Code/*.lean)
register_simp_attr rv_word
-- rv_state: reading pc / registers / memory of a state built by set / next / jump / store; literal normal form
register_simp_attr rv_state
-- rv_side: unfolding for side conditions (memory map, alignment)
register_simp_attr rv_side
-- rv_exec: one execution step (fetch, decode, per-kind exec, memory read-after-write)
register_simp_attr rv_exec
