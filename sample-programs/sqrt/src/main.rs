#[link(wasm_import_module = "env")]
unsafe extern "C" {
    pub safe fn read_u32(idx: u32) -> u32;
    pub safe fn abort();
}

pub fn main() {
    let n: u32 = read_u32(0);
    let r: u32 = read_u32(1);
    if r * r != n {
        abort();
    }
}
