pub(crate) mod capacity;
mod census;
mod kernels;

pub(crate) use kernels::*;

#[cfg(test)]
mod reference;
#[cfg(test)]
mod tests;

#[doc(hidden)]
pub use census::dr_tail_first_order_mismatch;
