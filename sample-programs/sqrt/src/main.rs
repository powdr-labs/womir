#[link(wasm_import_module = "env")]
unsafe extern "C" {
    pub safe fn read_u32() -> u32;
    pub safe fn abort();
}

pub fn main() {
    let n: u32 = read_u32();
    let r: u32 = read_u32();
    if r * r != n {
        abort();
    }
}
