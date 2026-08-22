pub(crate) mod binding;
// The generated registry carries each entry's symbol name for the drift guard;
// production dispatch reads only the mask and the function pointer.
#[allow(dead_code)]
pub(crate) mod generated_registry;
#[doc(hidden)]
pub mod reference;
pub(crate) mod tail;

#[cfg(test)]
mod tests;
