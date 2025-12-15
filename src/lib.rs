use wasmparser::ValType;

use crate::loader::{settings::Settings, word_count_type};

pub mod generic_ir;
pub mod interpreter;
pub mod linker;
pub mod loader;
pub mod utils;

/// Returns the number of words needed to store the given types.
pub fn word_count_types<'a, S: Settings<'a>>(types: &[ValType]) -> u32 {
    types.iter().map(|ty| word_count_type::<S>(*ty)).sum()
}
