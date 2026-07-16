//! Simulated cache residency (spec M2 §2, dead-aware per M3 §2): one lane
//! pool shared by cached values and open stash slots. Stashes are
//! unevictable; cached values are always evictable. Victim selection order
//! is `(is_live, priority, ExprId)`: dead (exhausted — no future readers)
//! residents go first regardless of priority, since a dead value is worth
//! nothing to keep around; among live residents the M2 rule is unchanged
//! (strictly-lower-priority, lowest (priority, ExprId) first, over a
//! BTreeMap for fixed iteration order). The protected in-flight set
//! (`admit`'s `protected` argument) outranks deadness — an in-flight operand
//! is never evicted for the duration of that call, dead or not. Marking a
//! value dead never triggers a new eviction by itself: it only changes which
//! resident gets picked when a displacement was going to happen anyway.

use std::collections::BTreeMap;

use cs::gkr_compiler::dag_ir::ExprId;

#[derive(Debug, Clone, Copy)]
struct Resident {
    width: u32,
    priority: u32,
    dead: bool,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Admit {
    Admitted { victims: Vec<ExprId> },
    Refused,
}

pub struct Residency {
    budget: Option<u32>,
    resident: BTreeMap<ExprId, Resident>,
    resident_lanes: u32,
    stash_lanes: u32,
}

impl Residency {
    pub fn new(budget: Option<u32>) -> Self {
        Residency { budget, resident: BTreeMap::new(), resident_lanes: 0, stash_lanes: 0 }
    }

    pub fn is_resident(&self, e: ExprId) -> bool {
        self.resident.contains_key(&e)
    }

    /// Marks a resident as dead (exhausted — no future readers per the
    /// walker's liveness tracking): it becomes a first-pick victim (see
    /// `victim_order`) regardless of its priority, but stays resident (and
    /// still readable) until something actually displaces it. Does not
    /// evict anything itself.
    pub fn mark_dead(&mut self, e: ExprId) {
        self.resident
            .get_mut(&e)
            .unwrap_or_else(|| {
                panic!("gkr_flatten residency: mark_dead on non-resident {e:?} — walker deadness sync bug")
            })
            .dead = true;
    }

    /// Current residents as `(ExprId, width, dead)`, in deterministic
    /// BTreeMap (ExprId) order. Consumed by the walker/scheduler to key
    /// decisions on which values are resident and dead vs. still live.
    pub fn residents(&self) -> impl Iterator<Item = (ExprId, u32, bool)> + '_ {
        self.resident.iter().map(|(&e, r)| (e, r.width, r.dead))
    }

    pub fn stash_lanes(&self) -> u32 {
        self.stash_lanes
    }

    pub fn resident_lanes(&self) -> u32 {
        self.resident_lanes
    }

    fn free_lanes(&self) -> Option<u32> {
        self.budget.map(|b| b - self.stash_lanes - self.resident_lanes)
    }

    /// Residents sorted dead-first, then lowest (priority, ExprId) — the
    /// deterministic victim order for both admission pressure and stash
    /// pressure. `!r.dead` sorts `false` (dead) before `true` (live), so
    /// every dead resident precedes every live one; ties within each group
    /// break by (priority, ExprId) as in M2.
    fn victim_order(&self) -> Vec<(bool, u32, ExprId, u32)> {
        let mut v: Vec<(bool, u32, ExprId, u32)> =
            self.resident.iter().map(|(&e, r)| (!r.dead, r.priority, e, r.width)).collect();
        v.sort(); // (is_live, priority, ExprId, width): ExprId tiebreak by derive(Ord)
        v
    }

    fn evict(&mut self, e: ExprId) {
        let r = self.resident.remove(&e).expect("victim must be resident");
        self.resident_lanes -= r.width;
    }

    /// Spec §2 post-mutation tripwire: the lane pool (stash + resident) must
    /// never exceed the budget. This already holds by construction — every
    /// mutation site checks/reclaims lanes before committing — so this is a
    /// debug-only assert of an invariant, not a new behavior.
    fn debug_check(&self) {
        if let Some(b) = self.budget {
            debug_assert!(
                self.stash_lanes + self.resident_lanes <= b,
                "gkr_flatten residency: lane pool overflow (model bug)"
            );
        }
    }

    /// Admits `e` (width lanes, `priority`) into the pool, evicting the
    /// lowest strictly-lower-priority residents as needed. `protected` names
    /// residents that must NOT be evicted for the duration of THIS call — the
    /// walker uses it to pin an already-resolved sibling operand (in flight,
    /// pending an emit) so admitting its partner can never displace a value a
    /// not-yet-pushed op still reads. A protected candidate is skipped during
    /// victim collection (as if it were higher-priority); if skipping it
    /// leaves too few reclaimable lanes, the admission refuses untouched
    /// (check-before-mutate). Victim order is otherwise dead-first, then
    /// deterministic lowest-(priority, ExprId): a dead resident is always a
    /// valid victim regardless of the incomer's priority (it is worth
    /// nothing to keep), while a live resident still needs strictly-lower
    /// priority than the incomer, exactly as in M2.
    pub fn admit(&mut self, e: ExprId, width: u32, priority: u32, protected: &[ExprId]) -> Admit {
        assert!(
            !self.is_resident(e),
            "gkr_flatten residency: {e:?} already resident — the walker must hit-check before \
             recomputing/re-admitting (model bug)"
        );
        let Some(free) = self.free_lanes() else {
            // Unbounded: always admit, never evict.
            self.resident.insert(e, Resident { width, priority, dead: false });
            self.resident_lanes += width;
            self.debug_check();
            return Admit::Admitted { victims: vec![] };
        };
        let mut victims = Vec::new();
        if width > free {
            // Check-before-mutate: collect victims in dead-first,
            // (priority, ExprId) order (skipping any protected in-flight
            // operand) until enough lanes free up; if impossible, refuse
            // untouched. A dead candidate is always taken; a live candidate
            // only if it is strictly lower priority than the incomer —
            // otherwise stop (sound: dead sorts first, so once a blocking
            // live candidate is hit, every later candidate is live with
            // priority >= that one).
            let mut reclaimable = 0u32;
            for (is_live, p, v, w) in self.victim_order() {
                if protected.contains(&v) {
                    continue; // in-flight sibling operand: unevictable this call
                }
                if is_live && p >= priority {
                    break;
                }
                victims.push(v);
                reclaimable += w;
                if free + reclaimable >= width {
                    break;
                }
            }
            if free + reclaimable < width {
                return Admit::Refused;
            }
            for &v in &victims {
                self.evict(v);
            }
        }
        self.resident.insert(e, Resident { width, priority, dead: false });
        self.resident_lanes += width;
        self.debug_check();
        Admit::Admitted { victims }
    }

    /// Reserves `lanes` stash lanes, evicting residents (dead-first, then
    /// lowest priority, unconditionally — stashes outrank every cached
    /// value) as needed. Panics if the pool cannot satisfy the reservation:
    /// the load-time peak assert guarantees stash demand always fits, so
    /// this is a model-bug tripwire, not error handling.
    pub fn reserve_stash(&mut self, lanes: u32) -> Vec<ExprId> {
        let mut victims = Vec::new();
        if let Some(budget) = self.budget {
            assert!(
                self.stash_lanes + lanes <= budget,
                "gkr_flatten residency: stash demand {} exceeds budget {budget} — the load-time \
                 peak assert must have been skipped (model bug)",
                self.stash_lanes + lanes
            );
            let mut free = budget - self.stash_lanes - self.resident_lanes;
            if free < lanes {
                for (_, _, v, w) in self.victim_order() {
                    victims.push(v);
                    free += w;
                    if free >= lanes {
                        break;
                    }
                }
                for &v in &victims {
                    self.evict(v);
                }
            }
        }
        self.stash_lanes += lanes;
        self.debug_check();
        victims
    }

    pub fn release_stash(&mut self, lanes: u32) {
        debug_assert!(lanes <= self.stash_lanes);
        self.stash_lanes -= lanes;
        self.debug_check();
    }
}

#[cfg(test)]
mod tests {
    use cs::gkr_compiler::dag_ir::ExprId;

    use super::*;

    #[test]
    fn admit_within_free_space_no_victims() {
        let mut r = Residency::new(Some(8));
        assert_eq!(r.admit(ExprId(1), 4, 10, &[]), Admit::Admitted { victims: vec![] });
        assert!(r.is_resident(ExprId(1)));
        assert_eq!(r.resident_lanes(), 4);
    }

    #[test]
    fn eviction_lowest_priority_first_exprid_tiebreak() {
        let mut r = Residency::new(Some(8));
        r.admit(ExprId(1), 4, 5, &[]);
        r.admit(ExprId(2), 4, 5, &[]);
        // Incoming priority 9 > 5: evicts strictly-lower residents, lowest
        // (priority, ExprId) first — ExprId(1) before ExprId(2).
        assert_eq!(r.admit(ExprId(3), 4, 9, &[]), Admit::Admitted { victims: vec![ExprId(1)] });
        assert!(!r.is_resident(ExprId(1)));
        assert!(r.is_resident(ExprId(2)));
    }

    #[test]
    fn equal_priority_refuses() {
        let mut r = Residency::new(Some(4));
        r.admit(ExprId(1), 4, 5, &[]);
        // Strictly-lower rule: an equal-priority incomer would itself be lowest.
        assert_eq!(r.admit(ExprId(2), 4, 5, &[]), Admit::Refused);
        assert!(r.is_resident(ExprId(1)));
    }

    #[test]
    fn refuse_when_higher_priority_residents_block() {
        let mut r = Residency::new(Some(4));
        r.admit(ExprId(1), 4, 9, &[]);
        assert_eq!(r.admit(ExprId(2), 4, 5, &[]), Admit::Refused);
    }

    #[test]
    fn wide_incomer_evicts_multiple() {
        let mut r = Residency::new(Some(8));
        r.admit(ExprId(1), 4, 1, &[]);
        r.admit(ExprId(2), 4, 2, &[]);
        assert_eq!(
            r.admit(ExprId(3), 8, 9, &[]),
            Admit::Admitted { victims: vec![ExprId(1), ExprId(2)] }
        );
    }

    #[test]
    fn partial_eviction_refuses_and_mutates_nothing() {
        let mut r = Residency::new(Some(8));
        r.admit(ExprId(1), 4, 1, &[]);
        r.admit(ExprId(2), 4, 9, &[]);
        // Needs 8 lanes; only ExprId(1) (4 lanes) is strictly lower -> refuse,
        // and BOTH residents must survive (check-before-mutate).
        assert_eq!(r.admit(ExprId(3), 8, 5, &[]), Admit::Refused);
        assert!(r.is_resident(ExprId(1)) && r.is_resident(ExprId(2)));
    }

    #[test]
    fn protected_victim_is_skipped_and_admission_refuses() {
        // Baseline (unprotected): a priority-9 incomer evicts the lone
        // strictly-lower resident to make room.
        let mut r = Residency::new(Some(4));
        r.admit(ExprId(1), 4, 1, &[]);
        assert_eq!(
            r.admit(ExprId(2), 4, 9, &[]),
            Admit::Admitted { victims: vec![ExprId(1)] }
        );
        assert!(!r.is_resident(ExprId(1)));

        // Protected: the SAME admission may not touch ExprId(1) (its only
        // viable victim), so it refuses untouched and ExprId(1) survives.
        let mut r = Residency::new(Some(4));
        r.admit(ExprId(1), 4, 1, &[]);
        assert_eq!(r.admit(ExprId(2), 4, 9, &[ExprId(1)]), Admit::Refused);
        assert!(r.is_resident(ExprId(1)), "protected resident survives");
        assert!(!r.is_resident(ExprId(2)), "blocked incomer is not admitted");
    }

    #[test]
    fn stash_reservation_evicts_residents() {
        let mut r = Residency::new(Some(8));
        r.admit(ExprId(1), 4, 100, &[]); // even max-priority residents lose to stash
        r.admit(ExprId(2), 4, 1, &[]);
        let victims = r.reserve_stash(8);
        assert_eq!(victims, vec![ExprId(2), ExprId(1)]); // lowest (priority, id) first
        assert_eq!(r.stash_lanes(), 8);
        r.release_stash(8);
        assert_eq!(r.stash_lanes(), 0);
    }

    #[test]
    #[should_panic(expected = "peak assert")]
    fn stash_overflow_panics() {
        let mut r = Residency::new(Some(4));
        r.reserve_stash(8); // no residents to evict, budget 4 < 8 -> model bug
    }

    #[test]
    #[should_panic(expected = "already resident")]
    fn duplicate_admission_panics() {
        let mut r = Residency::new(Some(8));
        r.admit(ExprId(1), 4, 1, &[]);
        r.admit(ExprId(1), 4, 1, &[]);
    }

    #[test]
    fn unbounded_never_evicts_or_refuses() {
        let mut r = Residency::new(None);
        for i in 0..1000u32 {
            assert_eq!(r.admit(ExprId(i), 4, 0, &[]), Admit::Admitted { victims: vec![] });
        }
        assert_eq!(r.reserve_stash(1_000_000), vec![]);
    }

    #[test]
    fn dead_evicted_before_live_regardless_of_priority() {
        let mut r = Residency::new(Some(8));
        r.admit(ExprId(1), 4, 9, &[]); // high priority
        r.admit(ExprId(2), 4, 1, &[]); // low priority
        r.mark_dead(ExprId(1));
        // Incomer at priority 5: M2 semantics would evict ExprId(2) (lowest
        // priority). Dead-first: ExprId(1) goes despite its priority 9.
        assert_eq!(r.admit(ExprId(3), 4, 5, &[]), Admit::Admitted { victims: vec![ExprId(1)] });
        assert!(r.is_resident(ExprId(2)));
    }

    #[test]
    fn dead_reclaimable_by_lower_priority_incomer() {
        let mut r = Residency::new(Some(4));
        r.admit(ExprId(1), 4, 9, &[]);
        r.mark_dead(ExprId(1));
        // M2 semantics: priority 1 < 9 -> Refused. Dead values are worthless:
        // any admission may reclaim them.
        assert_eq!(r.admit(ExprId(2), 4, 1, &[]), Admit::Admitted { victims: vec![ExprId(1)] });
    }

    #[test]
    fn live_residents_still_need_strictly_lower_priority() {
        let mut r = Residency::new(Some(4));
        r.admit(ExprId(1), 4, 5, &[]);
        // No dead residents: the M2 strictly-lower rule is unchanged.
        assert_eq!(r.admit(ExprId(2), 4, 5, &[]), Admit::Refused);
    }

    #[test]
    fn protected_dead_resident_survives() {
        let mut r = Residency::new(Some(4));
        r.admit(ExprId(1), 4, 1, &[]);
        r.mark_dead(ExprId(1));
        // Protection outranks deadness (the in-flight fma-operand window).
        assert_eq!(r.admit(ExprId(2), 4, 9, &[ExprId(1)]), Admit::Refused);
        assert!(r.is_resident(ExprId(1)));
    }

    #[test]
    fn stash_pressure_prefers_dead_victims() {
        let mut r = Residency::new(Some(8));
        r.admit(ExprId(1), 4, 1, &[]); // live, lowest priority
        r.admit(ExprId(2), 4, 9, &[]);
        r.mark_dead(ExprId(2));
        assert_eq!(r.reserve_stash(4), vec![ExprId(2)]); // dead beats low-priority live
        assert!(r.is_resident(ExprId(1)));
    }

    #[test]
    #[should_panic(expected = "mark_dead")]
    fn mark_dead_non_resident_panics() {
        let mut r = Residency::new(Some(8));
        r.mark_dead(ExprId(1));
    }

    #[test]
    fn residents_iterator_reports_width_and_deadness() {
        let mut r = Residency::new(Some(8));
        r.admit(ExprId(2), 4, 1, &[]);
        r.admit(ExprId(1), 1, 2, &[]);
        r.mark_dead(ExprId(2));
        let v: Vec<_> = r.residents().collect();
        assert_eq!(v, vec![(ExprId(1), 1, false), (ExprId(2), 4, true)]); // BTreeMap order
    }
}
