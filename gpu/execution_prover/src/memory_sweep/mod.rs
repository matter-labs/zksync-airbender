pub(crate) mod factory;
pub mod l1;
pub(crate) mod model;
mod probe;
mod runner;

pub fn main_entry() -> Result<(), Box<dyn std::error::Error>> {
    runner::main_entry()
}
