#[link(wasm_import_module = "env")]
unsafe extern "C" {
    pub fn read_u32_ext() -> u32;
    pub fn abort_ext();
}

fn read_u32() -> u32 {
    unsafe { read_u32_ext() }
}

fn abort() {
    unsafe { abort_ext() }
}

pub fn main() {
    let n: u32 = read_u32();
    let r: u32 = read_u32();
    if r * r != n {
        abort();
    }
}
