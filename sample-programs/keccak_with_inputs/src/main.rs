#[link(wasm_import_module = "env")]
unsafe extern "C" {
    pub safe fn read_u32(idx: u32) -> u32;
    pub safe fn abort();
}

use tiny_keccak::{Hasher, Keccak};

pub fn main() {
    let n: u32 = read_u32(0);
    let expected_first_byte: u32 = read_u32(1);

    let mut output = [0u8; 32];
    for _ in 0..n {
        let mut hasher = Keccak::v256();
        hasher.update(&output);
        hasher.finalize(&mut output);
    }

    assert_eq!(output[0] as u32, expected_first_byte);
}
