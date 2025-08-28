//! Run with, e.g.:
//! womir vec_median.wasm vec_median "" 5,11,15,75,6,5,1,4,7,3,2,9,2

#[link(wasm_import_module = "env")]
unsafe extern "C" {
    pub safe fn read_u32() -> u32;
}

#[unsafe(no_mangle)]
pub fn vec_median() {
    // let expected = read_u32();
    let len = read_u32();

    // WORKS
    // let mut vec = vec![];
    // for i in 0..len {
    //     vec.push(i);
    // }

    // DOESNT WORK
    let mut vec: Vec<_> = (0..len).collect();

    let elem = vec[2];
}
