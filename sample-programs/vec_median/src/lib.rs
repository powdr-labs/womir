//! Run with, e.g.:
//! womir vec_median.wasm vec_median "" 5,11,15,75,6,5,1,4,7,3,2,9,2

#[link(wasm_import_module = "env")]
unsafe extern "C" {
    pub safe fn read_u32(x: u32) -> u32;
}

#[unsafe(no_mangle)]
pub fn vec_median() {
    let expected = read_u32(0);
    let len = read_u32(1);

    let mut vec: Vec<_> = (2..(len + 2)).map(|idx| read_u32(idx)).collect();
    vec.sort();

    let half = (len / 2) as usize;
    let median = if len & 1 == 1 {
        vec[half]
    } else {
        (vec[half - 1] + vec[half]) / 2
    };

    print!("Found median of {median}\n");
    assert_eq!(median, expected);
}
