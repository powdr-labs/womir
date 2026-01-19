use crate::loader;

/// Trait controlling the behavior of the flattening process.
///
/// TODO: find a way to make calling conventions and interface registers allocation
/// part of this trait.
pub trait Settings<'a>: loader::Settings {
    type Directive;
}
