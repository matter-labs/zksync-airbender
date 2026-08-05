//! Backward fragment decomposition (CS-M5a Task 1, spec §3): the pure,
//! side-effect-free walk that decomposes a backward alpha-spine's addends
//! into FRAGMENTS — `acc = c_init + Σ recipe_i · value(fragment_i)` — so a
//! later stage (Task 2+) can lower each fragment's value once and its
//! summed coefficient recipe cheaply.
//!
//! Ported from the proven reference classifier
//! `.agents/experiments/2026-07-13-bwd-order-eviction/wsdump/src/bin/fragclass.rs`
//! (`analyze()`), adapted to build the real IR (not just stats) over this
//! crate's distilled-arena types ([`DagLayer`]/[`Expr`]/[`ExprId`]).
//!
//! Normative walk semantics:
//!  1. `scalar_pure` is a bottom-up per-expr flag: `Constant`/`Challenge`
//!     leaves are scalar-pure; an `Add`/`Mul` is scalar-pure iff every child
//!     is. `VirtualSetup` and every other `Source` kind (`Read`,
//!     `LookupValue`) are NEVER scalar-pure, regardless of shape.
//!  2. The spine addends are walked with an `(id, chain)` stack, `chain`
//!     being the accumulated scalar-pure factors seen so far (a
//!     [`ProductRecipe`] in progress):
//!       - `id` scalar-pure -> its value (chain ++ id) is a [`C_init`]
//!         contribution (`c_init` field).
//!       - `Add(children)` -> push every child with the SAME chain
//!         (occurrences are NEVER deduped — `A + A` walks `A` twice).
//!       - `Mul(_)` -> FLATTEN the whole Mul-nest first (scalar-pure
//!         factors at any depth are absorbed into the chain; non-scalar
//!         factors become sorted value atoms). If exactly one non-scalar
//!         atom remains AND it is an `Add`, DISTRIBUTE (push its children
//!         with the enriched chain, linearizing `c·(x+y) = c·x + c·y`).
//!         Otherwise, emit one fragment occurrence keyed by the sorted
//!         atom multiset (no distribution inside multi-atom products, even
//!         if one atom happens to be an `Add`).
//!       - bare non-scalar `Source` -> emit a singleton-atom fragment
//!         occurrence.
//!  3. Occurrences are merged by their sorted `atoms` (the fragment's value
//!     key): each occurrence appends its chain as one term of the
//!     fragment's [`MergedRecipe`] (sum of products; never collapsed —
//!     `A + A` yields ONE fragment with TWO empty-factor terms, not a
//!     single doubled term).
//!  4. [`MergedRecipe::is_trivial`] holds iff the recipe is exactly the
//!     scalar `1` (one term, no factors).
//!
//! [`C_init`]: FragmentTable::c_init

use std::collections::BTreeMap;

use gkr_eval_ir::{DagLayer, Expr, ExprId, SourceKind};

// ── Recipe / fragment types ──────────────────────────────────────────────────

/// A product of scalar-pure distilled expressions (`Constant`/`Challenge`
/// leaves, or Add/Mul closures thereof — see module docs). Empty = the
/// multiplicative identity `1`.
#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct ProductRecipe {
    pub factors: Vec<ExprId>,
}

/// A sum of [`ProductRecipe`] terms (`Σ Π factors`). Empty = the additive
/// identity `0`. Terms are never merged/collapsed across occurrences: two
/// identical unit ("1") terms stay two terms, not one term "2" (see
/// `repeated_operands_keep_multiplicity` below).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MergedRecipe {
    pub terms: Vec<ProductRecipe>,
}

/// One backward fragment: a non-scalar value (`atoms`, sorted ascending —
/// either a single Source/Add root, or the sorted factor multiset of an
/// opaque multi-atom product) paired with the summed coefficient recipe it
/// is read under, across every additive occurrence found in the spine.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FragmentSpec {
    pub atoms: Vec<ExprId>,
    pub recipe: MergedRecipe,
}

/// The full decomposition of a backward spine:
/// `acc = c_init + Σ_i fragments[i].recipe · value(fragments[i].atoms)`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct FragmentTable {
    pub fragments: Vec<FragmentSpec>,
    pub c_init: MergedRecipe,
}

// ── decompose_spine ───────────────────────────────────────────────────────────

/// Decompose `spine` (the addend roots of a backward alpha-spine, or any
/// list of expr roots over `layer`) into a [`FragmentTable`] per the
/// normative walk documented above.
pub fn decompose_spine(layer: &DagLayer, spine: &[ExprId]) -> FragmentTable {
    let exprs = &layer.exprs;
    let sources = &layer.sources;

    // 1. Bottom-up scalar-purity. `exprs` is arena order (children always
    // intern before parents), so a single forward pass suffices.
    let mut scalar_pure = vec![false; exprs.len()];
    for (i, expr) in exprs.iter().enumerate() {
        scalar_pure[i] = match expr {
            Expr::Source(s) => matches!(
                sources[s.0 as usize].kind,
                SourceKind::Constant { .. } | SourceKind::Challenge { .. }
            ),
            Expr::Add(ch) | Expr::Mul(ch) => ch.iter().all(|c| scalar_pure[c.0 as usize]),
        };
    }
    let is_pure = |id: ExprId| scalar_pure[id.0 as usize];

    // 2. Multiplicative flatten of the Mul-nest rooted at `root`: scalar-pure
    // subterms (any depth) are absorbed as coefficient factors; everything
    // else becomes a sorted value atom. Add nodes reached here are NOT
    // descended into (they become opaque atoms, possibly re-examined by the
    // distribute check below).
    let flatten = |root: ExprId| -> (Vec<ExprId>, Vec<ExprId>) {
        let mut atoms = Vec::new();
        let mut absorbed = Vec::new();
        let mut stack = vec![root];
        while let Some(id) = stack.pop() {
            if is_pure(id) {
                absorbed.push(id);
                continue;
            }
            match &exprs[id.0 as usize] {
                Expr::Mul(ch) => stack.extend(ch.iter().copied()),
                _ => atoms.push(id),
            }
        }
        atoms.sort();
        (atoms, absorbed)
    };

    // 3. Unified walk over the spine addends.
    let mut frags: Vec<(Vec<ExprId>, Vec<ExprId>)> = Vec::new();
    let mut c_init_terms: Vec<ProductRecipe> = Vec::new();
    let mut occurrences: usize = 0;
    // Final-review T1-M1: this single shared `(id, chain)` stack is semantically
    // equivalent to the reference classifier's per-term stack (one stack per spine
    // addend) — LIFO popping never interleaves chains across addends, since each
    // pushed entry carries its own complete `chain` snapshot.
    let mut work: Vec<(ExprId, Vec<ExprId>)> = spine.iter().map(|&t| (t, Vec::new())).collect();
    while let Some((id, chain)) = work.pop() {
        if is_pure(id) {
            let mut factors = chain;
            factors.push(id);
            factors.sort();
            c_init_terms.push(ProductRecipe { factors });
            occurrences += 1;
            assert!(
                occurrences < 100_000,
                "fragment decomposition occurrence guard exceeded"
            );
            continue;
        }
        match &exprs[id.0 as usize] {
            Expr::Add(ch) => {
                for &c in ch {
                    work.push((c, chain.clone()));
                }
            }
            Expr::Mul(_) => {
                let (atoms, absorbed) = flatten(id);
                let mut enriched = chain;
                enriched.extend(absorbed);
                if atoms.len() == 1 && matches!(&exprs[atoms[0].0 as usize], Expr::Add(_)) {
                    // Linearize c·(x+y) = c·x + c·y: distribute into the
                    // single non-scalar Add atom with the enriched chain.
                    work.push((atoms[0], enriched));
                } else {
                    enriched.sort();
                    frags.push((atoms, enriched));
                    occurrences += 1;
                    assert!(
                        occurrences < 100_000,
                        "fragment decomposition occurrence guard exceeded"
                    );
                }
            }
            Expr::Source(_) => {
                let mut sig = chain;
                sig.sort();
                frags.push((vec![id], sig));
                occurrences += 1;
                assert!(
                    occurrences < 100_000,
                    "fragment decomposition occurrence guard exceeded"
                );
            }
        }
    }

    // 4. Merge occurrences by sorted `atoms` (the value key); each
    // occurrence appends its chain as one MergedRecipe term.
    let mut merged: BTreeMap<Vec<ExprId>, Vec<ProductRecipe>> = BTreeMap::new();
    for (atoms, chain) in frags {
        merged
            .entry(atoms)
            .or_default()
            .push(ProductRecipe { factors: chain });
    }
    let fragments = merged
        .into_iter()
        .map(|(atoms, terms)| FragmentSpec {
            atoms,
            recipe: MergedRecipe { terms },
        })
        .collect();

    FragmentTable {
        fragments,
        c_init: MergedRecipe {
            terms: c_init_terms,
        },
    }
}

// ── Tests ────────────────────────────────────────────────────────────────────
