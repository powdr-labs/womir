#[unsafe(no_mangle)]
pub fn vec_median(len: u32) {
    let mut vec = vec![];
    for i in 0..len {
        vec.push(i);
    }
}
