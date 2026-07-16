//! Simulated cache residency (spec M2 §2): one lane pool shared by cached
//! values and open stash slots. Stashes are unevictable; cached values are
//! always evictable. All victim selection is deterministic: lowest
//! (priority, ExprId) first, over a BTreeMap (fixed iteration order).

use std::collections::BTreeMap;

use cs::gkr_compiler::dag_ir::ExprId;

#[derive(Debug, Clone, Copy)]
struct Resident {
    width: u32,
    priority: u32,
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

    pub fn stash_lanes(&self) -> u32 {
        self.stash_lanes
    }

    pub fn resident_lanes(&self) -> u32 {
        self.resident_lanes
    }

    fn free_lanes(&self) -> Option<u32> {
        self.budget.map(|b| b - self.stash_lanes - self.resident_lanes)
    }

    /// Residents sorted lowest (priority, ExprId) first — the deterministic
    /// victim order for both admission pressure and stash pressure.
    fn victim_order(&self) -> Vec<(u32, ExprId, u32)> {
        let mut v: Vec<(u32, ExprId, u32)> =
            self.resident.iter().map(|(&e, r)| (r.priority, e, r.width)).collect();
        v.sort(); // (priority, ExprId, width): ExprId tiebreak by derive(Ord)
        v
    }

    fn evict(&mut self, e: ExprId) {
        let r = self.resident.remove(&e).expect("victim must be resident");
        self.resident_lanes -= r.width;
    }

    pub fn admit(&mut self, e: ExprId, width: u32, priority: u32) -> Admit {
        assert!(
            !self.is_resident(e),
            "gkr_flatten residency: {e:?} already resident — the walker must hit-check before \
             recomputing/re-admitting (model bug)"
        );
        let Some(free) = self.free_lanes() else {
            // Unbounded: always admit, never evict.
            self.resident.insert(e, Resident { width, priority });
            self.resident_lanes += width;
            return Admit::Admitted { victims: vec![] };
        };
        let mut victims = Vec::new();
        if width > free {
            // Check-before-mutate: collect strictly-lower-priority victims
            // until enough lanes free up; if impossible, refuse untouched.
            let mut reclaimable = 0u32;
            for (p, v, w) in self.victim_order() {
                if p >= priority {
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
        self.resident.insert(e, Resident { width, priority });
        self.resident_lanes += width;
        Admit::Admitted { victims }
    }

    /// Reserves `lanes` stash lanes, evicting residents (lowest priority
    /// first, unconditionally — stashes outrank every cached value) as
    /// needed. Panics if the pool cannot satisfy the reservation: the
    /// load-time peak assert guarantees stash demand always fits, so this is
    /// a model-bug tripwire, not error handling.
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
                for (_, v, w) in self.victim_order() {
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
        victims
    }

    pub fn release_stash(&mut self, lanes: u32) {
        debug_assert!(lanes <= self.stash_lanes);
        self.stash_lanes -= lanes;
    }
}

#[cfg(test)]
mod tests {
    use cs::gkr_compiler::dag_ir::ExprId;

    use super::*;

    #[test]
    fn admit_within_free_space_no_victims() {
        let mut r = Residency::new(Some(8));
        assert_eq!(r.admit(ExprId(1), 4, 10), Admit::Admitted { victims: vec![] });
        assert!(r.is_resident(ExprId(1)));
        assert_eq!(r.resident_lanes(), 4);
    }

    #[test]
    fn eviction_lowest_priority_first_exprid_tiebreak() {
        let mut r = Residency::new(Some(8));
        r.admit(ExprId(1), 4, 5);
        r.admit(ExprId(2), 4, 5);
        // Incoming priority 9 > 5: evicts strictly-lower residents, lowest
        // (priority, ExprId) first — ExprId(1) before ExprId(2).
        assert_eq!(r.admit(ExprId(3), 4, 9), Admit::Admitted { victims: vec![ExprId(1)] });
        assert!(!r.is_resident(ExprId(1)));
        assert!(r.is_resident(ExprId(2)));
    }

    #[test]
    fn equal_priority_refuses() {
        let mut r = Residency::new(Some(4));
        r.admit(ExprId(1), 4, 5);
        // Strictly-lower rule: an equal-priority incomer would itself be lowest.
        assert_eq!(r.admit(ExprId(2), 4, 5), Admit::Refused);
        assert!(r.is_resident(ExprId(1)));
    }

    #[test]
    fn refuse_when_higher_priority_residents_block() {
        let mut r = Residency::new(Some(4));
        r.admit(ExprId(1), 4, 9);
        assert_eq!(r.admit(ExprId(2), 4, 5), Admit::Refused);
    }

    #[test]
    fn wide_incomer_evicts_multiple() {
        let mut r = Residency::new(Some(8));
        r.admit(ExprId(1), 4, 1);
        r.admit(ExprId(2), 4, 2);
        assert_eq!(
            r.admit(ExprId(3), 8, 9),
            Admit::Admitted { victims: vec![ExprId(1), ExprId(2)] }
        );
    }

    #[test]
    fn partial_eviction_refuses_and_mutates_nothing() {
        let mut r = Residency::new(Some(8));
        r.admit(ExprId(1), 4, 1);
        r.admit(ExprId(2), 4, 9);
        // Needs 8 lanes; only ExprId(1) (4 lanes) is strictly lower -> refuse,
        // and BOTH residents must survive (check-before-mutate).
        assert_eq!(r.admit(ExprId(3), 8, 5), Admit::Refused);
        assert!(r.is_resident(ExprId(1)) && r.is_resident(ExprId(2)));
    }

    #[test]
    fn stash_reservation_evicts_residents() {
        let mut r = Residency::new(Some(8));
        r.admit(ExprId(1), 4, 100); // even max-priority residents lose to stash
        r.admit(ExprId(2), 4, 1);
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
        r.admit(ExprId(1), 4, 1);
        r.admit(ExprId(1), 4, 1);
    }

    #[test]
    fn unbounded_never_evicts_or_refuses() {
        let mut r = Residency::new(None);
        for i in 0..1000u32 {
            assert_eq!(r.admit(ExprId(i), 4, 0), Admit::Admitted { victims: vec![] });
        }
        assert_eq!(r.reserve_stash(1_000_000), vec![]);
    }
}
