use wasmparser::ValType;

use crate::loader::{settings::Settings, wom::flattening::word_count_type};

pub mod loader;
pub mod utils;
pub mod wom_interpreter;

/// Returns the number of words needed to store the given types.
pub fn word_count_types<'a, S: Settings<'a>>(types: &[ValType]) -> u32 {
    types.iter().map(|ty| word_count_type::<S>(*ty)).sum()
}
