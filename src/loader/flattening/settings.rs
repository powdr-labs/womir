/// Trait controlling the behavior of the flattening process.
pub trait Settings {
    //type Directive;

    fn bytes_per_word() -> u32;

    /// The size, in words, of a pointer to an executable ROM address,
    /// and a pointer to a frame.
    fn words_per_ptr() -> u32;
}
