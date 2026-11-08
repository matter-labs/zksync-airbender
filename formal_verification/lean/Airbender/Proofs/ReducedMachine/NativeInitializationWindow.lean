import Airbender.Proofs.ReducedMachine.NativeInitializationAddressParser

namespace Airbender.NativeInitializationWindowProofs
open Airbender.NativeInitializationWindow Airbender.NativeInitializationBoundary Airbender.NativeInitializationOrdering
open Airbender.ReducedMachine.Native Airbender.ReducedMachine.NativeMainAuxiliary
open Airbender.ReducedMachine.NativeMemoryBoundary Airbender.Blake2Worker.Native
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem window_choice {previous current : PublicValues}
    (lastBounds : previous.oneBeforeLast[0].val < 65536 ∧ previous.oneBeforeLast[1].val < 65536)
    (firstBounds : current.first[0].val < 65536 ∧ current.first[1].val < 65536)
    (accepted : WindowAccepted previous current) :
    addressValue previous.oneBeforeLast < addressValue current.first ∨ previous.oneBeforeLast = #v[0,0,0,0,0,0] := by
  unfold WindowAccepted at accepted
  rw [NativeInitializationAddressParserProofs.parsed lastBounds,NativeInitializationAddressParserProofs.parsed firstBounds] at accepted
  simp only [NativeInitializationAddressParserProofs.parsed_value lastBounds,NativeInitializationAddressParserProofs.parsed_value firstBounds] at accepted
  split_ifs at accepted with strict
  · exact Or.inl strict
  · right
    obtain ⟨zero,fields⟩ := accepted
    have lowVal : previous.oneBeforeLast[0].val = 0 := by unfold addressValue at zero; omega
    have highVal : previous.oneBeforeLast[1].val = 0 := by unfold addressValue at zero; omega
    have low : previous.oneBeforeLast[0] = 0 := (ZMod.val_eq_zero _).mp lowVal
    have high : previous.oneBeforeLast[1] = 0 := (ZMod.val_eq_zero _).mp highVal
    apply Vector.ext
    intro i bound
    by_cases lo : i = 0
    · subst i; exact low
    by_cases hi : i = 1
    · subst i; exact high
    have slot : i-2 < 4 := by omega
    have h := fields ⟨i-2,slot⟩
    have target : (#v[(0 : F),0,0,0,0,0])[i] = 0 := by interval_cases i <;> rfl
    rw [target]
    simpa only [show i-2+2 = i by omega] using h

theorem record_zero_padding {w : Nat → F} (zero : record w = #v[0,0,0,0,0,0]) : PaddingRecord w := by
  have fields : #v[w 126,w 127,w 128,w 129,w 130,w 131] = #v[(0 : F),0,0,0,0,0] := by
    rw [← (NativeInitializationBoundaryProofs.geometry w).1]; exact zero
  intro column member
  rw [Airbender.ReducedMachine.NativeMainAuxiliaryProofs.initialization_geometry.2.2.2] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact congrArg (fun v : Vector F 6 => v[0]) fields
  · exact congrArg (fun v : Vector F 6 => v[1]) fields
  · exact congrArg (fun v : Vector F 6 => v[2]) fields
  · exact congrArg (fun v : Vector F 6 => v[3]) fields
  · exact congrArg (fun v : Vector F 6 => v[4]) fields
  · exact congrArg (fun v : Vector F 6 => v[5]) fields

/-- Zero terminal fallback plus actual strict sorting derives that EVERY previous
    ordinary record is padding, rather than assuming an empty/padded chunk. -/
theorem zero_terminal_padding {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (gamma : R)
    {proof : Airbender.NativeScalar16Arguments.Proof R} {values : PublicValues}
    (accepted : Airbender.NativeInitializationBoundary.Accepted embed memory pc gamma proof values)
    (zero : values.oneBeforeLast = #v[0,0,0,0,0,0]) :
    ∀ i < scalar16Layout.traceLength-1, PaddingRecord (proof.initialization.main.rows i) := by
  have last : record (proof.initialization.main.rows (scalar16Layout.traceLength-2)) = #v[0,0,0,0,0,0] :=
    (NativeInitializationBoundaryProofs.endpoint accepted.oneBeforeLast).trans zero
  intro i bound
  by_cases terminal : i = scalar16Layout.traceLength-2
  · subst i; exact record_zero_padding last
  · by_contra nonpadding
    have strict := NativeInitializationBoundaryProofs.strict_terminal embed memory pc gamma accepted i (by omega) nonpadding
    rw [zero] at strict
    have empty : addressValue (#v[(0 : F),0,0,0,0,0]) = 0 := by decide +kernel
    rw [empty] at strict
    omega

theorem fallback_rows {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (gamma : R)
    {previous current : Chunk R}
    (left : Airbender.NativeInitializationBoundary.Accepted embed memory pc gamma previous.proof previous.values)
    (right : Airbender.NativeInitializationBoundary.Accepted embed memory pc gamma current.proof current.values)
    (window : WindowAccepted previous.values current.values)
    (fallback : ¬ addressValue previous.values.oneBeforeLast < addressValue current.values.first) :
    ∀ i < scalar16Layout.traceLength-1, PaddingRecord (previous.proof.initialization.main.rows i) := by
  have lBounds := NativeInitializationBoundaryProofs.public_bounds embed memory pc gamma left
  have rBounds := NativeInitializationBoundaryProofs.public_bounds embed memory pc gamma right
  have choice := window_choice ⟨lBounds.2.2.1,lBounds.2.2.2⟩ ⟨rBounds.1,rBounds.2.1⟩ window
  exact zero_terminal_padding embed memory pc gamma left (choice.resolve_left fallback)

theorem adjacent_rows {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (gamma : R)
    {previous current : Chunk R}
    (left : Airbender.NativeInitializationBoundary.Accepted embed memory pc gamma previous.proof previous.values)
    (right : Airbender.NativeInitializationBoundary.Accepted embed memory pc gamma current.proof current.values)
    (window : WindowAccepted previous.values current.values) :
    ∀ i < scalar16Layout.traceLength-1, ∀ j < scalar16Layout.traceLength-1,
      Airbender.NativeInitializationSorted.addressValue (previous.proof.initialization.main.rows i) ≤
        Airbender.NativeInitializationSorted.addressValue (current.proof.initialization.main.rows j) ∧
      (¬ PaddingRecord (previous.proof.initialization.main.rows i) →
        Airbender.NativeInitializationSorted.addressValue (previous.proof.initialization.main.rows i) <
          Airbender.NativeInitializationSorted.addressValue (current.proof.initialization.main.rows j)) := by
  have lBounds := NativeInitializationBoundaryProofs.public_bounds embed memory pc gamma left
  have rBounds := NativeInitializationBoundaryProofs.public_bounds embed memory pc gamma right
  have choice := window_choice ⟨lBounds.2.2.1,lBounds.2.2.2⟩ ⟨rBounds.1,rBounds.2.1⟩ window
  intro i ib j jb
  have lInterval := NativeInitializationBoundaryProofs.public_interval embed memory pc gamma left i ib
  have rInterval := NativeInitializationBoundaryProofs.public_interval embed memory pc gamma right j jb
  rcases choice with strict | zero
  · have order := Nat.lt_of_le_of_lt lInterval.2 (Nat.lt_of_lt_of_le strict rInterval.1)
    exact ⟨Nat.le_of_lt order,fun _ => order⟩
  · have padded := zero_terminal_padding embed memory pc gamma left zero i ib
    have value := NativeInitializationSortedProofs.padding_address padded
    exact ⟨by omega,fun nonpadding => False.elim (nonpadding padded)⟩

/-- Entire ABSTRACT finite chunk induction before concrete native objects/domain.
    Every intermediate chunk remains in the ordering, including all padding. -/
theorem cross_sequence {count rows : Nat} {value : Nat → Nat → Nat} {padding : Nat → Nat → Prop}
    (positive : 0 < rows)
    (adjacent : ∀ c, c + 1 < count → ∀ i < rows, ∀ j < rows,
      value c i ≤ value (c + 1) j ∧ (¬ padding c i → value c i < value (c + 1) j)) :
    ∀ c d, c < d → d < count → ∀ i < rows, ∀ j < rows,
      value c i ≤ value d j ∧ (¬ padding c i → value c i < value d j) := by
  intro c d
  induction d with
  | zero => intro order; omega
  | succ d ih =>
    intro order bound i ib j jb
    by_cases same : c = d
    · subst c; exact adjacent d bound i ib j jb
    · have previous := ih (by omega) (by omega) i ib 0 positive
      have next := adjacent d bound 0 positive j jb
      exact ⟨Nat.le_trans previous.1 next.1,fun nonpadding => Nat.lt_of_lt_of_le (previous.2 nonpadding) next.1⟩

theorem global_rows {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (gamma : R)
    {count : Nat} {chunks : Nat → Chunk R}
    (accepted : Airbender.NativeInitializationWindow.Accepted embed memory pc gamma count chunks) :
    ∀ c d, c < d → d < count → ∀ i < scalar16Layout.traceLength-1, ∀ j < scalar16Layout.traceLength-1,
      Airbender.NativeInitializationSorted.addressValue ((chunks c).proof.initialization.main.rows i) ≤
        Airbender.NativeInitializationSorted.addressValue ((chunks d).proof.initialization.main.rows j) ∧
      (¬ PaddingRecord ((chunks c).proof.initialization.main.rows i) →
        Airbender.NativeInitializationSorted.addressValue ((chunks c).proof.initialization.main.rows i) <
          Airbender.NativeInitializationSorted.addressValue ((chunks d).proof.initialization.main.rows j)) := by
  exact cross_sequence (by decide +kernel) (fun c bound => adjacent_rows embed memory pc gamma
    (accepted.components c (by omega)) (accepted.components (c + 1) bound) (accepted.windows c bound))

theorem global_token_unique {R : Type} [Field R] (embed : F →+* R)
    (memory : MemoryKeyChallenges R) (pc : PCChallenges R) (gamma : R)
    {count : Nat} {chunks : Nat → Chunk R}
    (accepted : Airbender.NativeInitializationWindow.Accepted embed memory pc gamma count chunks)
    (c d i j : Nat) (cb : c < count) (db : d < count)
    (ib : i < scalar16Layout.traceLength-1) (jb : j < scalar16Layout.traceLength-1)
    (ip : ¬ PaddingRecord ((chunks c).proof.initialization.main.rows i))
    (jp : ¬ PaddingRecord ((chunks d).proof.initialization.main.rows j))
    (same : (Airbender.NativeMemoryTokens.encodeKey (initializationKey ((chunks c).proof.initialization.main.rows i) true)).address =
      (Airbender.NativeMemoryTokens.encodeKey (initializationKey ((chunks d).proof.initialization.main.rows j) true)).address) : c = d ∧ i = j := by
  have raw := NativeInitializationOrderingProofs.token_address_binding same
  have value := congrArg (fun v : Vector F 2 => v[0].val+65536*v[1].val) raw
  change Airbender.NativeInitializationSorted.addressValue ((chunks c).proof.initialization.main.rows i) =
    Airbender.NativeInitializationSorted.addressValue ((chunks d).proof.initialization.main.rows j) at value
  rcases lt_trichotomy c d with less | equal | greater
  · have strict := (global_rows embed memory pc gamma accepted c d less db i ib j jb).2 ip
    omega
  · subst d
    exact ⟨rfl,NativeInitializationSortedProofs.token_unique embed memory pc gamma
      (accepted.components c cb).scalar i j ib jb ip jp same⟩
  · have strict := (global_rows embed memory pc gamma accepted d c greater cb j jb i ib).2 jp
    omega

end Airbender.NativeInitializationWindowProofs
