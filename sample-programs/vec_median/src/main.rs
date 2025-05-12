#[link(wasm_import_module = "env")]
unsafe extern "C" {
    pub fn read_u32_base(x: u32) -> u32;
}

fn read_u32(x: u32) -> u32 {
    unsafe { read_u32_base(x) }
}

fn main() {
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
