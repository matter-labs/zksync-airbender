mod binding;
mod composition;

// Task 4 consumes the R0 surface; D1/DR-cont consumes the continuation surface.
#[allow(unused_imports)]
pub(crate) use binding::{DrCompactSourceTableBuilder, DrWindowBindError};
#[allow(unused_imports)]
pub(crate) use composition::{DrWindowPassEqState, DrWindowRawInputKeepalive};

#[cfg(test)]
mod tests;
