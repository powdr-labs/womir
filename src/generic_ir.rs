use crate::loader::flattening;

pub struct GenericIrSetting {}

impl flattening::Settings for GenericIrSetting {
    fn bytes_per_word() -> u32 {
        4
    }

    fn words_per_ptr() -> u32 {
        1
    }
}
