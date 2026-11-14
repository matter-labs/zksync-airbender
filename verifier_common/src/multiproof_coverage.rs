//! Native-only query-branch counts for preverified Miri inputs.
use std::cell::RefCell;

std::thread_local! {
    static QUERIES: RefCell<Vec<usize>> = const { RefCell::new(Vec::new()) };
}

pub fn reset() {
    QUERIES.with_borrow_mut(Vec::clear);
}

pub fn record(round: usize) {
    QUERIES.with_borrow_mut(|queries| {
        if queries.len() <= round {
            queries.resize(round + 1, 0);
        }
        queries[round] += 1;
    });
}

pub fn counts() -> Vec<usize> {
    QUERIES.with_borrow(Clone::clone)
}
