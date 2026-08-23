pub(crate) mod capacity;
mod census;

#[cfg(test)]
mod reference;
#[cfg(test)]
mod tests;

#[doc(hidden)]
pub use census::dr_tail_first_order_mismatch;
