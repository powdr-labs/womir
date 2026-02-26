use std::{
    fs::File,
    io::{BufWriter, Write},
};

use clap::{Parser, Subcommand};
use womir::{
    interpreter::{
        ExecutionModel, ExternalFunctions, Interpreter, MemoryAccessor,
        generic_ir::{Directive, GenericIrSetting},
    },
    loader::{FunctionAsm, PartiallyParsedProgram, Program, rwm::RWMStages, wom::WomStages},
};

// ============== GoJS runtime support ==============
// Go's WASM runtime communicates with JS through a set of syscalls.
// Each call receives SP (stack pointer) as the first argument and
// reads/writes parameters from the Go stack at SP+8, SP+16, etc.
//
// Go's JS value system uses NaN-boxing: values are 64-bit floats where
// NaN payloads encode references to non-numeric JS values.

use std::collections::HashMap;

const NAN_HEAD: u32 = 0x7FF80000;
const TYPE_FLAG_NONE: u32 = 0;
const TYPE_FLAG_OBJECT: u32 = 1;
const TYPE_FLAG_STRING: u32 = 2;
#[allow(dead_code)]
const TYPE_FLAG_SYMBOL: u32 = 3;
const TYPE_FLAG_FUNCTION: u32 = 4;

/// A JS value stored in our table.
#[derive(Clone, Debug)]
enum JsValue {
    Undefined,
    Null,
    Bool(bool),
    Number(f64),
    Object(HashMap<String, u32>), // property name -> value ID
    Function(String),             // function name for dispatch
    String(String),
    Uint8Array(Vec<u8>),
}

/// Encode a value ID + type flag into a 64-bit Go ref.
fn encode_ref(id: u32, type_flag: u32) -> u64 {
    ((NAN_HEAD as u64 | type_flag as u64) << 32) | id as u64
}

fn write_ref(mem: &mut MemoryAccessor<'_>, addr: u32, ref_val: u64) {
    mem.set_word(addr, ref_val as u32).unwrap();
    mem.set_word(addr + 4, (ref_val >> 32) as u32).unwrap();
}

fn read_ref(mem: &mut MemoryAccessor<'_>, addr: u32) -> u64 {
    let lo = mem.get_word(addr).unwrap() as u64;
    let hi = mem.get_word(addr + 4).unwrap() as u64;
    (hi << 32) | lo
}

/// Decode a ref into a value ID. Returns None for special values.
fn decode_ref_id(r: u64) -> Option<u32> {
    if r == 0 {
        return None; // undefined
    }
    // Check if it's a NaN-boxed reference
    let hi = (r >> 32) as u32;
    if hi & NAN_HEAD == NAN_HEAD {
        Some(r as u32) // lower 32 bits are the ID
    } else {
        None // it's a regular float number
    }
}

/// The JS value table.
struct JsValueTable {
    values: Vec<JsValue>,
    next_id: u32,
}

impl JsValueTable {
    fn new() -> Self {
        let mut t = Self {
            values: Vec::new(),
            next_id: 0,
        };

        // Predefined values (IDs 0-6 match Go's expectations):
        // ID 0: NaN
        t.add(JsValue::Number(f64::NAN));
        // ID 1: 0
        t.add(JsValue::Number(0.0));
        // ID 2: null
        t.add(JsValue::Null);
        // ID 3: true
        t.add(JsValue::Bool(true));
        // ID 4: false
        t.add(JsValue::Bool(false));
        // ID 5: global
        t.add(JsValue::Object(HashMap::new()));
        // ID 6: jsGo (this)
        t.add(JsValue::Object(HashMap::new()));

        // Now set up global properties (ID 5):
        let object_id = t.add(JsValue::Function("Object".into()));
        let array_id = t.add(JsValue::Function("Array".into()));
        let uint8array_id = t.add(JsValue::Function("Uint8Array".into()));

        // process object
        let process_id = t.add(JsValue::Object(HashMap::new()));
        // process.pid, process.ppid
        let num_zero = 1; // ID 1 = 0
        t.set_prop(process_id, "pid", num_zero);
        t.set_prop(process_id, "ppid", num_zero);

        // fs module
        let fs_id = t.add(JsValue::Object(HashMap::new()));
        let fs_write_id = t.add(JsValue::Function("fs.write".into()));
        let fs_read_id = t.add(JsValue::Function("fs.read".into()));
        let fs_open_id = t.add(JsValue::Function("fs.open".into()));
        let fs_close_id = t.add(JsValue::Function("fs.close".into()));
        let fs_fstat_id = t.add(JsValue::Function("fs.fstat".into()));
        let fs_mkdir_id = t.add(JsValue::Function("fs.mkdir".into()));

        // fs.constants - all POSIX open flags Go's syscall package expects
        let fs_constants_id = t.add(JsValue::Object(HashMap::new()));
        let add_const = |t: &mut JsValueTable, parent: u32, name: &str, val: f64| {
            let id = t.add(JsValue::Number(val));
            t.set_prop(parent, name, id);
        };
        add_const(&mut t, fs_constants_id, "O_RDONLY", 0.0);
        add_const(&mut t, fs_constants_id, "O_WRONLY", 1.0);
        add_const(&mut t, fs_constants_id, "O_RDWR", 2.0);
        add_const(&mut t, fs_constants_id, "O_CREAT", 64.0);
        add_const(&mut t, fs_constants_id, "O_EXCL", 128.0);
        add_const(&mut t, fs_constants_id, "O_NOCTTY", 256.0);
        add_const(&mut t, fs_constants_id, "O_TRUNC", 512.0);
        add_const(&mut t, fs_constants_id, "O_APPEND", 1024.0);
        add_const(&mut t, fs_constants_id, "O_NONBLOCK", 2048.0);
        add_const(&mut t, fs_constants_id, "O_DIRECTORY", 65536.0);
        add_const(&mut t, fs_constants_id, "O_NOFOLLOW", 131072.0);
        add_const(&mut t, fs_constants_id, "O_SYNC", 1052672.0);
        add_const(&mut t, fs_constants_id, "O_CLOEXEC", 524288.0);

        t.set_prop(fs_id, "write", fs_write_id);
        t.set_prop(fs_id, "read", fs_read_id);
        t.set_prop(fs_id, "open", fs_open_id);
        t.set_prop(fs_id, "close", fs_close_id);
        t.set_prop(fs_id, "fstat", fs_fstat_id);
        t.set_prop(fs_id, "mkdir", fs_mkdir_id);
        t.set_prop(fs_id, "constants", fs_constants_id);

        // path module (minimal)
        let path_id = t.add(JsValue::Object(HashMap::new()));

        // Set global properties
        t.set_prop(5, "Object", object_id);
        t.set_prop(5, "Array", array_id);
        t.set_prop(5, "Uint8Array", uint8array_id);
        t.set_prop(5, "process", process_id);
        t.set_prop(5, "fs", fs_id);
        t.set_prop(5, "path", path_id);

        // jsGo._pendingEvent (used by Go runtime)
        t.set_prop(6, "_pendingEvent", 2); // null

        t
    }

    fn add(&mut self, val: JsValue) -> u32 {
        let id = self.next_id;
        self.next_id += 1;
        if (id as usize) < self.values.len() {
            self.values[id as usize] = val;
        } else {
            assert_eq!(id as usize, self.values.len());
            self.values.push(val);
        }
        id
    }

    fn get(&self, id: u32) -> &JsValue {
        &self.values[id as usize]
    }

    fn set_prop(&mut self, obj_id: u32, name: &str, val_id: u32) {
        if let JsValue::Object(ref mut props) = self.values[obj_id as usize] {
            props.insert(name.to_string(), val_id);
        }
    }

    fn get_prop(&self, obj_id: u32, name: &str) -> Option<u32> {
        if let JsValue::Object(ref props) = self.values[obj_id as usize] {
            props.get(name).copied()
        } else {
            None
        }
    }

    /// Return the ref encoding for a given value ID.
    fn ref_for(&self, id: u32) -> u64 {
        match &self.values[id as usize] {
            JsValue::Undefined => 0,
            JsValue::Null => encode_ref(id, TYPE_FLAG_NONE),
            JsValue::Bool(_) => encode_ref(id, TYPE_FLAG_NONE),
            JsValue::Number(n) => {
                // Special cases: 0 and NaN are encoded as NaN-boxed refs
                if n.is_nan() || *n == 0.0 {
                    encode_ref(id, TYPE_FLAG_NONE)
                } else {
                    n.to_bits()
                }
            }
            JsValue::Object(_) => encode_ref(id, TYPE_FLAG_OBJECT),
            JsValue::Function(_) => encode_ref(id, TYPE_FLAG_FUNCTION),
            JsValue::String(_) => encode_ref(id, TYPE_FLAG_STRING),
            JsValue::Uint8Array(_) => encode_ref(id, TYPE_FLAG_OBJECT),
        }
    }
}

/// Helper to read an i64 from two consecutive i32 words in memory.
fn read_i64(mem: &mut MemoryAccessor<'_>, addr: u32) -> i64 {
    let lo = mem.get_word(addr).unwrap();
    let hi = mem.get_word(addr + 4).unwrap();
    ((hi as u64) << 32 | lo as u64) as i64
}

/// Helper to write an i64 as two consecutive i32 words in memory.
fn write_i64(mem: &mut MemoryAccessor<'_>, addr: u32, val: i64) {
    let val = val as u64;
    mem.set_word(addr, val as u32).unwrap();
    mem.set_word(addr + 4, (val >> 32) as u32).unwrap();
}

/// Helper to read a byte from memory.
fn read_byte(mem: &mut MemoryAccessor<'_>, addr: u32) -> u8 {
    let word = mem.get_word(addr & !3).unwrap();
    (word >> ((addr % 4) * 8)) as u8
}

/// Helper to write a byte to memory.
fn write_byte(mem: &mut MemoryAccessor<'_>, addr: u32, val: u8) {
    let aligned = addr & !3;
    let shift = (addr % 4) * 8;
    let existing = mem.get_word(aligned).unwrap();
    let mask = !(0xFFu32 << shift);
    let new_val = (existing & mask) | ((val as u32) << shift);
    mem.set_word(aligned, new_val).unwrap();
}

/// Helper to read bytes from memory.
fn read_bytes(mem: &mut MemoryAccessor<'_>, addr: u32, len: usize) -> Vec<u8> {
    (0..len).map(|i| read_byte(mem, addr + i as u32)).collect()
}

/// GoJS runtime state.
struct GoJsRuntime {
    values: JsValueTable,
}

impl GoJsRuntime {
    fn new() -> Self {
        Self {
            values: JsValueTable::new(),
        }
    }

    /// Handle a gojs syscall.
    fn call(&mut self, fname: &str, sp: u32, mem: &mut MemoryAccessor<'_>) {
        match fname {
            "runtime.wasmExit" => {
                let code = mem.get_word(sp + 8).unwrap();
                eprintln!("[gojs] wasmExit: code={code}");
            }
            "runtime.wasmWrite" => {
                let fd = mem.get_word(sp + 8).unwrap();
                let ptr = read_i64(mem, sp + 16) as u32;
                let len = mem.get_word(sp + 24).unwrap();
                if len > 0 {
                    let bytes = read_bytes(mem, ptr, len as usize);
                    let msg = String::from_utf8_lossy(&bytes);
                    if fd == 1 {
                        eprint!("{msg}"); // stdout
                    } else {
                        eprint!("{msg}"); // stderr
                    }
                }
            }
            "runtime.resetMemoryDataView" => {}
            "runtime.nanotime1" => {
                // Must return non-zero. Go checks this in runtime.main.
                static NANOTIME: std::sync::atomic::AtomicI64 =
                    std::sync::atomic::AtomicI64::new(1_000_000_000);
                let t = NANOTIME.fetch_add(1_000_000, std::sync::atomic::Ordering::Relaxed);
                write_i64(mem, sp + 8, t);
            }
            "runtime.walltime" => {
                write_i64(mem, sp + 8, 1_700_000_000); // seconds
                mem.set_word(sp + 16, 0).unwrap(); // nanos
            }
            "runtime.scheduleTimeoutEvent" => {
                // Return timer ID = -1 (no timer)
                write_i64(mem, sp + 16, -1);
            }
            "runtime.clearTimeoutEvent" => {}
            "runtime.getRandomData" => {
                let dst = read_i64(mem, sp + 8) as u32;
                let len = read_i64(mem, sp + 16) as u32;
                for i in 0..len {
                    write_byte(mem, dst + i, 0);
                }
            }
            "syscall/js.finalizeRef" => {}
            "syscall/js.stringVal" => {
                // Input: str ptr (i64 sp+8), str len (i64 sp+16)
                // Output: ref at sp+24
                let ptr = read_i64(mem, sp + 8) as u32;
                let len = read_i64(mem, sp + 16) as u32;
                let s = String::from_utf8_lossy(&read_bytes(mem, ptr, len as usize)).to_string();
                let id = self.values.add(JsValue::String(s));
                let r = self.values.ref_for(id);
                write_ref(mem, sp + 24, r);
            }
            "syscall/js.valueGet" => {
                // Input: ref (sp+8), prop name ptr (i64 sp+16), prop name len (i64 sp+24)
                // Output: ref at sp+32
                let obj_ref = read_ref(mem, sp + 8);
                let name_ptr = read_i64(mem, sp + 16) as u32;
                let name_len = read_i64(mem, sp + 24) as u32;
                let name =
                    String::from_utf8_lossy(&read_bytes(mem, name_ptr, name_len as usize))
                        .to_string();

                let result_ref = if let Some(obj_id) = decode_ref_id(obj_ref) {
                    if let Some(prop_id) = self.values.get_prop(obj_id, &name) {
                        self.values.ref_for(prop_id)
                    } else {
                        eprintln!(
                            "[gojs] valueGet: property '{name}' not found on object {obj_id}"
                        );
                        0 // undefined
                    }
                } else {
                    eprintln!("[gojs] valueGet: called on non-object ref {obj_ref:#x}");
                    0
                };
                write_ref(mem, sp + 32, result_ref);
            }
            "syscall/js.valueSet" => {
                // Input: ref (sp+8), prop name ptr (i64 sp+16), prop name len (i64 sp+24), value ref (sp+32)
                let obj_ref = read_ref(mem, sp + 8);
                let name_ptr = read_i64(mem, sp + 16) as u32;
                let name_len = read_i64(mem, sp + 24) as u32;
                let name =
                    String::from_utf8_lossy(&read_bytes(mem, name_ptr, name_len as usize))
                        .to_string();
                let val_ref = read_ref(mem, sp + 32);

                if let Some(obj_id) = decode_ref_id(obj_ref) {
                    if let Some(val_id) = decode_ref_id(val_ref) {
                        self.values.set_prop(obj_id, &name, val_id);
                    }
                }
                let _ = name; // suppress warning
            }
            "syscall/js.valueLength" => {
                // Return 0 for everything
                write_i64(mem, sp + 16, 0);
            }
            "syscall/js.valueIndex" => {
                // Return undefined
                write_ref(mem, sp + 24, 0);
            }
            "syscall/js.valuePrepareString" => {
                let val_ref = read_ref(mem, sp + 8);
                let (str_ref, str_len) = if let Some(id) = decode_ref_id(val_ref) {
                    if let JsValue::String(s) = self.values.get(id) {
                        (self.values.ref_for(id), s.len() as i64)
                    } else {
                        (encode_ref(id, TYPE_FLAG_STRING), 0)
                    }
                } else {
                    (0, 0)
                };
                write_ref(mem, sp + 16, str_ref);
                write_i64(mem, sp + 24, str_len);
            }
            "syscall/js.valueLoadString" => {
                // Input: ref at sp+8, dst slice (ptr i64 sp+16, len i64 sp+24)
                let val_ref = read_ref(mem, sp + 8);
                let dst_ptr = read_i64(mem, sp + 16) as u32;
                if let Some(id) = decode_ref_id(val_ref) {
                    if let JsValue::String(s) = self.values.get(id).clone() {
                        let bytes = s.as_bytes();
                        for (i, &b) in bytes.iter().enumerate() {
                            write_byte(mem, dst_ptr + i as u32, b);
                        }
                    }
                }
            }
            "syscall/js.valueNew" => {
                // Input: ref at sp+8 (constructor), args at sp+16
                // Output: ref at sp+40, ok bool at sp+48
                let ctor_ref = read_ref(mem, sp + 8);
                let result_id = if let Some(ctor_id) = decode_ref_id(ctor_ref) {
                    match self.values.get(ctor_id) {
                        JsValue::Function(name) if name == "Uint8Array" => {
                            // Read the length arg
                            let args_ptr = read_i64(mem, sp + 16) as u32;
                            let args_len = read_i64(mem, sp + 24) as u32;
                            let len = if args_len > 0 {
                                let arg_ref = read_ref(mem, args_ptr);
                                // If it's a float number, use it as length
                                let hi = (arg_ref >> 32) as u32;
                                if hi & NAN_HEAD != NAN_HEAD {
                                    f64::from_bits(arg_ref) as usize
                                } else {
                                    0
                                }
                            } else {
                                0
                            };
                            self.values.add(JsValue::Uint8Array(vec![0; len]))
                        }
                        JsValue::Function(name) if name == "Object" => {
                            self.values.add(JsValue::Object(HashMap::new()))
                        }
                        JsValue::Function(name) if name == "Array" => {
                            self.values.add(JsValue::Object(HashMap::new()))
                        }
                        _ => self.values.add(JsValue::Object(HashMap::new())),
                    }
                } else {
                    self.values.add(JsValue::Object(HashMap::new()))
                };
                let r = self.values.ref_for(result_id);
                write_ref(mem, sp + 40, r);
                write_byte(mem, sp + 48, 1); // ok = true
            }
            "syscall/js.valueCall" => {
                // Input: obj ref (sp+8), method name ptr (i64 sp+16), method name len (i64 sp+24),
                //        args ptr (i64 sp+32), args len (i64 sp+40)
                // Output: result ref at sp+56, ok bool at sp+64
                let _obj_ref = read_ref(mem, sp + 8);
                let method_ptr = read_i64(mem, sp + 16) as u32;
                let method_len = read_i64(mem, sp + 24) as u32;
                let method =
                    String::from_utf8_lossy(&read_bytes(mem, method_ptr, method_len as usize))
                        .to_string();
                let args_ptr = read_i64(mem, sp + 32) as u32;
                let args_len = read_i64(mem, sp + 40) as u32;

                eprintln!("[gojs] valueCall: method={method} args_len={args_len}");

                let result_ref = match method.as_str() {
                    "getTimezoneOffset" => {
                        // Return 0 (UTC)
                        0f64.to_bits()
                    }
                    "cwd" => {
                        let id = self.values.add(JsValue::String("/".into()));
                        self.values.ref_for(id)
                    }
                    "write" => {
                        // fs.write(fd, buf, offset, length, position, callback)
                        // args: [fd, buf_ref, offset, length, null, callback]
                        if args_len >= 4 {
                            let fd_ref = read_ref(mem, args_ptr);
                            let buf_ref = read_ref(mem, args_ptr + 8);
                            let _offset_ref = read_ref(mem, args_ptr + 16);
                            let length_ref = read_ref(mem, args_ptr + 24);

                            let fd = f64::from_bits(fd_ref) as u32;
                            let length = f64::from_bits(length_ref) as usize;

                            if let Some(buf_id) = decode_ref_id(buf_ref) {
                                if let JsValue::Uint8Array(data) = self.values.get(buf_id) {
                                    let end = length.min(data.len());
                                    let msg = String::from_utf8_lossy(&data[..end]);
                                    if fd == 1 || fd == 2 {
                                        eprint!("{msg}");
                                    }
                                }
                            }

                            // Call callback with (null, n_written)
                            if args_len >= 6 {
                                let cb_ref = read_ref(mem, args_ptr + 40);
                                // We'd need to actually invoke the callback, but for now
                                // Go will handle it via the event loop
                                let _ = cb_ref;
                            }
                        }
                        // Return number of bytes written
                        0u64 // undefined - Go doesn't use the return value for fs.write
                    }
                    _ => {
                        eprintln!("[gojs] valueCall: unhandled method '{method}'");
                        0 // undefined
                    }
                };
                write_ref(mem, sp + 56, result_ref);
                write_byte(mem, sp + 64, 1); // ok = true
            }
            "syscall/js.copyBytesToGo" => {
                // Input: dst slice (ptr i64 sp+8, len i64 sp+16, cap i64 sp+24),
                //        src ref (sp+32)
                // Output: n i64 at sp+40, ok bool at sp+48
                let dst_ptr = read_i64(mem, sp + 8) as u32;
                let dst_len = read_i64(mem, sp + 16) as usize;
                let src_ref = read_ref(mem, sp + 32);
                let mut n = 0usize;
                if let Some(src_id) = decode_ref_id(src_ref) {
                    if let JsValue::Uint8Array(data) = self.values.get(src_id).clone() {
                        n = dst_len.min(data.len());
                        for i in 0..n {
                            write_byte(mem, dst_ptr + i as u32, data[i]);
                        }
                    }
                }
                write_i64(mem, sp + 40, n as i64);
                write_byte(mem, sp + 48, 1); // ok
            }
            "syscall/js.copyBytesToJS" => {
                // Input: dst ref (sp+8), src slice (ptr i64 sp+16, len i64 sp+24)
                // Output: n i64 at sp+40, ok bool at sp+48
                let dst_ref = read_ref(mem, sp + 8);
                let src_ptr = read_i64(mem, sp + 16) as u32;
                let src_len = read_i64(mem, sp + 24) as usize;
                let mut n = 0usize;
                if let Some(dst_id) = decode_ref_id(dst_ref) {
                    let data = read_bytes(mem, src_ptr, src_len);
                    n = data.len();
                    self.values.values[dst_id as usize] = JsValue::Uint8Array(data);
                }
                write_i64(mem, sp + 40, n as i64);
                write_byte(mem, sp + 48, 1); // ok
            }
            "syscall/js.valueSetIndex" => {
                // NOP
            }
            _ => {
                eprintln!("[gojs] WARNING: unimplemented gojs call: {fname}");
            }
        }
    }
}

struct DataInput {
    values: <Vec<u32> as IntoIterator>::IntoIter,
    /// Pre-formatted hint items: each is `[byte_len, word0, word1, ...]`.
    hint_items: Vec<Vec<u32>>,
    hint_item_idx: usize,
    /// Word-level read cursor within the current hint item.
    hint_cursor: usize,
    /// GoJS runtime state.
    gojs: GoJsRuntime,
}

impl DataInput {
    fn new(values: Vec<u32>) -> Self {
        Self {
            values: values.into_iter(),
            hint_items: Vec::new(),
            hint_item_idx: 0,
            hint_cursor: 0,
            gojs: GoJsRuntime::new(),
        }
    }

    fn new_with_binary_inputs(values: Vec<u32>, binary_inputs: Vec<Vec<u8>>) -> Self {
        let hint_items = binary_inputs
            .iter()
            .map(|data| {
                let byte_len = data.len() as u32;
                let num_words = data.len().div_ceil(4);
                let mut words = Vec::with_capacity(1 + num_words);
                words.push(byte_len);
                for chunk in data.chunks(4) {
                    let mut word_bytes = [0u8; 4];
                    word_bytes[..chunk.len()].copy_from_slice(chunk);
                    words.push(u32::from_le_bytes(word_bytes));
                }
                words
            })
            .collect();
        Self {
            values: values.into_iter(),
            hint_items,
            hint_item_idx: 0,
            hint_cursor: 0,
            gojs: GoJsRuntime::new(),
        }
    }
}

impl ExternalFunctions for DataInput {
    fn call(
        &mut self,
        module: &str,
        function: &str,
        args: &[u32],
        mem: &mut Option<MemoryAccessor<'_>>,
    ) -> Vec<u32> {
        match (module, function) {
            ("env", "read_u32") => {
                vec![self.values.next().expect("Not enough input values")]
            }
            ("env", "__hint_input") => {
                assert!(
                    self.hint_item_idx < self.hint_items.len(),
                    "No more hint items (requested item {}, have {})",
                    self.hint_item_idx,
                    self.hint_items.len()
                );
                self.hint_cursor = 0;
                vec![]
            }
            ("env", "__hint_buffer") => {
                let ptr = args[0];
                let num_words = args[1] as usize;
                let item = &self.hint_items[self.hint_item_idx];
                assert!(
                    self.hint_cursor + num_words <= item.len(),
                    "hint_buffer: reading {} words at cursor {} but item only has {} words",
                    num_words,
                    self.hint_cursor,
                    item.len()
                );
                let mem = mem.as_mut().unwrap();
                for i in 0..num_words {
                    mem.set_word(ptr + (i as u32) * 4, item[self.hint_cursor + i])
                        .unwrap();
                }
                self.hint_cursor += num_words;
                // Advance to next item when fully consumed.
                if self.hint_cursor >= item.len() {
                    self.hint_item_idx += 1;
                }
                vec![]
            }
            ("env", "__debug_print") => {
                let ptr = args[0];
                let num_bytes = args[1] as usize;
                let mem = mem.as_mut().unwrap();
                let bytes: Vec<u8> = (0..num_bytes)
                    .map(|i| {
                        let addr = ptr + (i as u32);
                        let word = mem.get_word(addr & !3).unwrap();
                        (word >> ((addr % 4) * 8)) as u8
                    })
                    .collect();
                let msg = String::from_utf8_lossy(&bytes);
                eprintln!("[guest] {msg}");
                vec![]
            }
            ("env", "abort") => {
                panic!("Abort called with args: {:?}", args);
            }
            ("gojs", fname) => {
                let sp = args[0];
                self.gojs.call(fname, sp, mem.as_mut().unwrap());
                vec![]
            }
            _ => {
                panic!(
                    "External function not implemented: module: {module}, function: {function} with args: {:?}",
                    args
                );
            }
        }
    }
}

fn main() -> wasmparser::Result<()> {
    env_logger::init();

    fn parse_exec_model(s: &str) -> Result<ExecutionModel, String> {
        match s {
            "wom" | "write-once" => Ok(ExecutionModel::WriteOnceRegisters),
            "rw" | "infinite" => Ok(ExecutionModel::InfiniteRegisters),
            _ => Err(format!("Invalid execution model: {s}")),
        }
    }

    /// Simple CLI for the `womir` binary.
    ///
    /// Two subcommands are supported:
    ///   compile <wasm-file>
    ///   run <wasm-file> <function> --func-inputs 1,2 --data-inputs 3,4
    #[derive(Parser)]
    #[command(author, version, about = "womir tool: compile or run a Wasm file", long_about = None)]
    struct Cli {
        /// Execution model (wom = write-once registers, rw = infinite/read-write registers)
        #[arg(short = 'e', long = "exec-model", default_value = "wom", global = true, value_parser = parse_exec_model)]
        exec_model: ExecutionModel,
        #[command(subcommand)]
        command: Command,
    }

    #[derive(Subcommand)]
    enum Command {
        /// Load and process the Wasm file (writes IR dump)
        Compile {
            /// Path to the wasm file to load
            wasm_file: String,
        },

        /// Run a function from the Wasm file
        Run {
            /// Path to the wasm file to load
            wasm_file: String,

            /// Function name to execute
            function: String,

            /// Should print the execution trace
            #[arg(long)]
            trace: bool,

            /// Comma separated arguments for the function (u32)
            #[arg(short,long, value_delimiter = ',', value_parser = clap::value_parser!(u32))]
            args: Vec<u32>,

            /// Comma separated data inputs (u32)
            #[arg(short, long, value_delimiter = ',', value_parser = clap::value_parser!(u32))]
            inputs: Vec<u32>,

            /// Binary files to feed via the hint stream (__hint_input / __hint_buffer)
            #[arg(long)]
            binary_input_files: Vec<String>,
        },
    }

    let cli = Cli::parse();

    match cli.command {
        Command::Compile { wasm_file } => {
            let wasm_bytes = std::fs::read(&wasm_file).unwrap();
            let program = womir::loader::load_wasm(GenericIrSetting::default(), &wasm_bytes)?;
            let program = process_functions(cli.exec_model, program)?;

            if let Err(err) = dump_ir(&program) {
                log::error!("Failed to dump IR: {err}");
            }

            Ok(())
        }
        Command::Run {
            wasm_file,
            function,
            args,
            inputs,
            binary_input_files,
            trace,
        } => {
            let wasm_bytes = std::fs::read(&wasm_file).unwrap();
            let program = womir::loader::load_wasm(GenericIrSetting::default(), &wasm_bytes)?;
            let program = process_functions(cli.exec_model, program)?;

            if let Err(err) = dump_ir(&program) {
                log::error!("Failed to dump IR: {err}");
            }

            let binary_inputs: Vec<Vec<u8>> = binary_input_files
                .iter()
                .map(|path| {
                    std::fs::read(path).unwrap_or_else(|e| panic!("Failed to read {path}: {e}"))
                })
                .collect();
            let data_input = if binary_inputs.is_empty() {
                DataInput::new(inputs)
            } else {
                DataInput::new_with_binary_inputs(inputs, binary_inputs)
            };

            let mut interpreter = Interpreter::new(program, cli.exec_model, data_input, trace);
            log::info!("Executing function: {function}");
            let outputs = interpreter.run(&function, &args);
            log::info!("Outputs: {:?}", outputs);

            Ok(())
        }
    }
}

fn process_functions<'a>(
    exec_model: ExecutionModel,
    program: PartiallyParsedProgram<'a, GenericIrSetting<'a>>,
) -> wasmparser::Result<Program<'a, FunctionAsm<Directive<'a>>>> {
    match exec_model {
        ExecutionModel::InfiniteRegisters => {
            program.default_par_process_all_functions::<RWMStages<GenericIrSetting>>()
        }
        ExecutionModel::WriteOnceRegisters => {
            program.default_par_process_all_functions::<WomStages<GenericIrSetting>>()
        }
    }
}

fn dump_ir(program: &Program<FunctionAsm<Directive>>) -> std::io::Result<()> {
    let mut file = BufWriter::new(File::create("ir_dump.txt")?);
    for (i, func) in program.functions.iter().enumerate() {
        writeln!(file, "Function {i}:")?;
        for directive in &func.directives {
            writeln!(file, "  {directive}")?;
        }
    }
    file.flush()?;
    log::info!("IR dump written to ir_dump.txt");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde::Deserialize;
    use std::fs;
    use std::path::PathBuf;
    use std::process::Command;
    use tempfile::NamedTempFile;
    use test_log::test;
    use womir::interpreter::NULL_REF;

    fn test_interpreter(
        path: &str,
        main_function: &str,
        func_inputs: &[u32],
        data_inputs: Vec<u32>,
        outputs: &[u32],
    ) {
        println!(
            "Run function: {main_function} with inputs: {func_inputs:?} and data inputs: {data_inputs:?}"
        );
        let wasm_file = std::fs::read(path).unwrap();
        let program = womir::loader::load_wasm(GenericIrSetting::default(), &wasm_file).unwrap();

        let pipelines = [
            (
                ExecutionModel::WriteOnceRegisters,
                program
                    .clone()
                    .default_par_process_all_functions::<WomStages<GenericIrSetting>>()
                    .unwrap(),
            ),
            (
                ExecutionModel::InfiniteRegisters,
                program
                    .default_par_process_all_functions::<RWMStages<GenericIrSetting>>()
                    .unwrap(),
            ),
        ];

        for (exec_model, program) in pipelines {
            println!("Testing execution model: {exec_model:?}");
            let mut interpreter = Interpreter::new(
                program,
                exec_model,
                DataInput::new(data_inputs.clone()),
                false,
            );
            let got_output = interpreter.run(main_function, func_inputs);
            assert_eq!(got_output, outputs);
        }
    }

    fn test_interpreter_from_sample_programs(
        path: &str,
        main_function: &str,
        func_inputs: &[u32],
        data_inputs: Vec<u32>,
        outputs: &[u32],
    ) {
        let path = format!("{}/sample-programs/{path}", env!("CARGO_MANIFEST_DIR"));
        test_interpreter(&path, main_function, func_inputs, data_inputs, outputs);
    }

    /// This test requires the directory and the package name to be the same in `case`.
    fn test_interpreter_rust(
        case: &str,
        main_function: &str,
        func_inputs: &[u32],
        data_inputs: Vec<u32>,
        outputs: &[u32],
    ) {
        let path = format!("{}/sample-programs/{case}", env!("CARGO_MANIFEST_DIR"));
        build_wasm(&PathBuf::from(&path));
        let wasm_path = format!("{path}/target/wasm32-unknown-unknown/release/{case}.wasm",);
        test_interpreter(&wasm_path, main_function, func_inputs, data_inputs, outputs);
    }

    fn build_wasm(path: &PathBuf) {
        assert!(path.exists(), "Target directory does not exist: {path:?}",);

        let output = Command::new("cargo")
            .arg("build")
            .arg("--release")
            .arg("--target")
            .arg("wasm32-unknown-unknown")
            .current_dir(path)
            .output()
            .expect("Failed to run cargo build");

        if !output.status.success() {
            eprintln!("stderr:\n{}", String::from_utf8_lossy(&output.stderr));
            eprintln!("stdout:\n{}", String::from_utf8_lossy(&output.stdout));
        }

        assert!(output.status.success(), "cargo build failed for {path:?}",);
    }

    #[test]
    fn test_sqrt() {
        test_interpreter_rust("sqrt", "main", &[0, 0], vec![9, 3], &[0]);
    }

    #[test]
    fn test_vec_grow() {
        test_interpreter_rust("vec_grow", "vec_grow", &[5], vec![], &[]);
    }

    #[test]
    fn test_vec_median() {
        test_interpreter_rust(
            "vec_median",
            "vec_median",
            &[],
            vec![5, 11, 15, 75, 6, 5, 1, 4, 7, 3, 2, 9, 2],
            &[],
        );
    }

    #[test]
    fn test_keccak() {
        test_interpreter_rust("keccak", "main", &[0, 0], vec![], &[0]);
    }

    #[test]
    fn test_keccak_with_inputs() {
        test_interpreter_rust("keccak_with_inputs", "main", &[0, 0], vec![1, 0x29], &[0]);
        test_interpreter_rust("keccak_with_inputs", "main", &[0, 0], vec![2, 0x51], &[0]);
        test_interpreter_rust("keccak_with_inputs", "main", &[0, 0], vec![5, 0xf2], &[0]);
        test_interpreter_rust("keccak_with_inputs", "main", &[0, 0], vec![10, 0x9b], &[0]);
    }

    #[test]
    fn test_fib() {
        test_interpreter_from_sample_programs("fib_loop.wasm", "fib", &[10], vec![], &[55]);
    }

    #[test]
    fn test_add() {
        test_interpreter_from_sample_programs(
            "add.wasm",
            "add",
            &[666, (-624_i32) as u32],
            vec![],
            &[42],
        );
    }

    #[test]
    fn test_collatz() {
        test_interpreter_from_sample_programs("collatz.wasm", "collatz", &[1 << 22], vec![], &[22]);
        test_interpreter_from_sample_programs("collatz.wasm", "collatz", &[310], vec![], &[86]);
    }

    #[test]
    fn test_merkle_tree() {
        // Judging by the binary, this program comes from Rust, but I don't have its source code.
        test_interpreter_from_sample_programs("merkle-tree.wasm", "main", &[0, 0], vec![], &[0]);
    }

    #[test]
    fn test_keeper_js() {
        // This is program is a stripped down version of geth, compiled for Go's js target.
        // Source: https://github.com/ethereum/go-ethereum/tree/master/cmd/keeper
        // Compile command:
        //   GOOS=js GOARCH=wasm go -gcflags=all=-d=softfloat build -tags "example" -o keeper.wasm
        test_interpreter_with_binary_inputs("keeper_js.wasm", "run", &[0, 0], &[], &[]);
    }

    #[test]
    fn test_keeper_js_with_payload() {
        // Run keeper_js with the hoodi block payload.
        test_interpreter_with_binary_inputs(
            "keeper_js.wasm",
            "run",
            &[0, 0],
            &["keeper/hoodi_payload.bin"],
            &[],
        );
    }

    /// Like `test_interpreter_from_sample_programs` but feeds binary files as hint stream inputs.
    fn test_interpreter_with_binary_inputs(
        wasm_path: &str,
        main_function: &str,
        func_inputs: &[u32],
        binary_input_paths: &[&str],
        outputs: &[u32],
    ) {
        let base = format!("{}/sample-programs", env!("CARGO_MANIFEST_DIR"));
        let wasm_file =
            std::fs::read(format!("{base}/{wasm_path}")).expect("failed to read wasm file");
        let binary_inputs: Vec<Vec<u8>> = binary_input_paths
            .iter()
            .map(|p| std::fs::read(format!("{base}/{p}")).expect("failed to read binary input"))
            .collect();

        let program = womir::loader::load_wasm(GenericIrSetting::default(), &wasm_file).unwrap();

        let program = program
            .default_par_process_all_functions::<RWMStages<GenericIrSetting>>()
            .unwrap();

        let mut interpreter = Interpreter::new(
            program,
            ExecutionModel::InfiniteRegisters,
            DataInput::new_with_binary_inputs(vec![], binary_inputs),
            false,
        );
        let got_output = interpreter.run(main_function, func_inputs);
        assert_eq!(got_output, outputs);
    }

    #[test]
    fn test_reth_guest_block_1() {
        // Executes Ethereum block 1 inside the reth guest compiled to wasm32.
        // The guest reads block input via the hint stream, executes the block, and verifies the
        // state root and post-execution checks.
        test_interpreter_with_binary_inputs(
            "reth-guest.wasm",
            "main",
            &[0, 0],
            &["reth-block-1.bin"],
            &[0],
        );
    }

    #[test]
    #[ignore] // ~7.5 MB input, takes a long time
    fn test_reth_guest_block_24171377() {
        // Executes Ethereum block 24171377 inside the reth guest compiled to wasm32.
        test_interpreter_with_binary_inputs(
            "reth-guest.wasm",
            "main",
            &[0, 0],
            &["reth-block-24171377.bin"],
            &[0],
        );
    }

    #[test]
    fn test_wasm_address() {
        test_wasm("wasm_testsuite/address.wast", None);
    }

    #[test]
    fn test_wasm_align() {
        test_wasm("wasm_testsuite/align.wast", None);
    }

    #[test]
    fn test_wasm_block() {
        test_wasm("wasm_testsuite/block.wast", None);
    }

    #[test]
    fn test_wasm_br_if() {
        test_wasm("wasm_testsuite/br_if.wast", None);
    }

    #[test]
    fn test_wasm_br_table() {
        test_wasm("wasm_testsuite/br_table.wast", None);
    }

    #[test]
    fn test_wasm_br() {
        test_wasm("wasm_testsuite/br.wast", None);
    }

    #[test]
    fn test_wasm_call() {
        test_wasm("wasm_testsuite/call.wast", None);
    }

    #[test]
    fn test_wasm_data() {
        test_wasm("wasm_testsuite/data.wast", None);
    }

    #[test]
    fn test_wasm_call_indirect() {
        test_wasm("wasm_testsuite/call_indirect.wast", None);
    }

    #[test]
    fn test_wasm_func() {
        test_wasm("wasm_testsuite/func.wast", None);
    }

    #[test]
    fn test_wasm_i32() {
        test_wasm("wasm_testsuite/i32.wast", None);
    }

    #[test]
    fn test_wasm_forward() {
        test_wasm("wasm_testsuite/forward.wast", None);
    }

    #[test]
    fn test_wasm_i64() {
        test_wasm("wasm_testsuite/i64.wast", None);
    }

    #[test]
    fn test_wasm_if() {
        test_wasm("wasm_testsuite/if.wast", None);
    }

    #[test]
    fn test_wasm_labels() {
        test_wasm("wasm_testsuite/labels.wast", None);
    }

    #[test]
    fn test_wasm_load() {
        test_wasm("wasm_testsuite/load.wast", None);
    }

    #[test]
    fn test_wasm_local_get() {
        test_wasm("wasm_testsuite/local_get.wast", None);
    }

    #[test]
    fn test_wasm_local_set() {
        test_wasm("wasm_testsuite/local_set.wast", None);
    }

    #[test]
    fn test_wasm_local_tee() {
        test_wasm("wasm_testsuite/local_tee.wast", None);
    }

    #[test]
    fn test_wasm_loop() {
        test_wasm("wasm_testsuite/loop.wast", None);
    }

    #[test]
    fn test_wasm_memory_fill() {
        test_wasm("wasm_testsuite/memory_fill.wast", None);
    }

    #[test]
    fn test_wasm_ref_is_null() {
        test_wasm("wasm_testsuite/ref_is_null.wast", None);
    }

    #[test]
    fn test_wasm_ref_null() {
        test_wasm("wasm_testsuite/ref_null.wast", None);
    }

    #[test]
    fn test_wasm_return() {
        test_wasm("wasm_testsuite/return.wast", None);
    }

    #[test]
    fn test_wasm_switch() {
        test_wasm("wasm_testsuite/switch.wast", None);
    }

    #[test]
    fn test_wasm_stack() {
        test_wasm("wasm_testsuite/stack.wast", None);
    }

    #[test]
    fn test_wasm_start() {
        test_wasm("wasm_testsuite/start.wast", None);
    }

    #[test]
    fn test_wasm_store() {
        test_wasm("wasm_testsuite/store.wast", None);
    }

    #[test]
    fn test_wasm_select() {
        test_wasm("wasm_testsuite/select.wast", None);
    }

    #[test]
    fn test_wasm_unwind() {
        test_wasm("wasm_testsuite/unwind.wast", None);
    }

    struct SpectestExternalFunctions;

    impl ExternalFunctions for SpectestExternalFunctions {
        fn call(
            &mut self,
            module: &str,
            function: &str,
            args: &[u32],
            _mem: &mut Option<MemoryAccessor<'_>>,
        ) -> Vec<u32> {
            /* From https://github.com/WebAssembly/spec/tree/main/interpreter#spectest-host-module
            (func (export "print"))
            (func (export "print_i32") (param i32))
            (func (export "print_i64") (param i64))
            (func (export "print_f32") (param f32))
            (func (export "print_f64") (param f64))
            (func (export "print_i32_f32") (param i32 f32))
            (func (export "print_f64_f64") (param f64 f64))
            */
            assert_eq!(module, "spectest", "Unexpected module: {module}");
            match function {
                "print" => println!(),
                "print_i32" => println!("{}", args[0] as i32),
                "print_i64" => println!("{}", (args[0] as u64 & ((args[1] as u64) << 32)) as i64),
                "print_f32" => println!("{}", f32::from_bits(args[0])),
                "print_f64" => println!(
                    "{}",
                    f64::from_bits((args[0] as u64) | ((args[1] as u64) << 32))
                ),
                "print_i32_f32" => {
                    println!("{} {}", args[0] as i32, f32::from_bits(args[1]))
                }
                "print_f64_f64" => {
                    println!(
                        "{} {}",
                        f64::from_bits(args[0] as u64 | ((args[1] as u64) << 32)),
                        f64::from_bits(args[2] as u64 | ((args[3] as u64) << 32))
                    )
                }
                _ => panic!(
                    "Unexpected function: {function} in module {module} with args: {:?}",
                    args
                ),
            }
            Vec::new()
        }
    }

    fn test_wasm(case: &str, functions: Option<&[&str]>) {
        match extract_wast_test_info(case) {
            Ok(modules) => {
                for (mod_name, line, asserts) in modules {
                    println!("Testing module: {} at line {line}", mod_name.display());
                    let wasm_file = std::fs::read(mod_name).unwrap();
                    let program =
                        womir::loader::load_wasm(GenericIrSetting::default(), &wasm_file).unwrap();

                    // TODO: change the processing stages interface so we can process the common
                    // stages just once, and resume for each independent pipeline (WOM and RWM).
                    let pipelines = [
                        (
                            program
                                .clone()
                                .default_par_process_all_functions::<RWMStages<GenericIrSetting>>()
                                .unwrap(),
                            ExecutionModel::InfiniteRegisters,
                        ),
                        (
                            program
                                .default_par_process_all_functions::<WomStages<GenericIrSetting>>()
                                .unwrap(),
                            ExecutionModel::WriteOnceRegisters,
                        ),
                    ];

                    for (program, exec_model) in pipelines {
                        println!("  Execution model: {:?}", exec_model);
                        let mut interpreter =
                            Interpreter::new(program, exec_model, SpectestExternalFunctions, false);

                        asserts
                            .iter()
                            .filter(|assert_case| {
                                if let Some(functions) = functions {
                                    functions.contains(&assert_case.function_name.as_str())
                                } else {
                                    true
                                }
                            })
                            .for_each(|assert_case| {
                                println!("Assert test case: {assert_case:#?}");
                                let got_output =
                                    interpreter.run(&assert_case.function_name, &assert_case.args);
                                assert_eq!(got_output, assert_case.expected);
                            });
                    }
                }
            }
            Err(e) => panic!("Error extracting wast test info: {e}"),
        }
    }

    #[derive(Debug, Deserialize)]
    struct TestFile {
        commands: Vec<CommandEntry>,
    }

    #[derive(Debug, Deserialize)]
    #[serde(tag = "type")]
    enum CommandEntry {
        #[serde(rename = "module")]
        Module { filename: String, line: usize },
        #[serde(rename = "assert_return")]
        AssertReturn {
            action: Action,
            expected: Vec<Val>,
            line: usize,
        },
        #[serde(rename = "action")]
        Action {
            action: Action,
            expected: Vec<Val>,
            line: usize,
        },
        #[serde(other)]
        Other,
    }

    #[derive(Debug)]
    pub struct AssertCase {
        pub function_name: String,
        pub args: Vec<u32>,
        pub expected: Vec<u32>,
        pub _line: usize,
    }

    #[derive(Debug, Deserialize)]
    pub struct Action {
        #[serde(rename = "type")]
        _action_type: String,
        field: Option<String>,
        args: Option<Vec<Val>>,
    }

    #[derive(Debug, Deserialize)]
    pub struct Val {
        #[serde(rename = "type")]
        val_type: String,
        value: serde_json::Value,
    }

    // TODO: refactor complex type
    #[allow(clippy::type_complexity)]
    pub fn extract_wast_test_info(
        wast_path: &str,
    ) -> Result<Vec<(PathBuf, usize, Vec<AssertCase>)>, Box<dyn std::error::Error>> {
        let temp_file = NamedTempFile::with_prefix("test")?;
        let Some(parent_dir) = temp_file.path().parent() else {
            panic!("Could not determine parent directory.");
        };
        let json_output_path = temp_file.path().to_owned();

        let output = Command::new("wast2json")
            .arg(wast_path)
            .arg("-o")
            .arg(json_output_path.clone())
            .output()?;

        if !output.status.success() {
            return Err(format!(
                "wast2json failed: {}",
                String::from_utf8_lossy(&output.stderr)
            )
            .into());
        }

        let json_text = fs::read_to_string(json_output_path)?;
        let test_file: TestFile = serde_json::from_str(&json_text)?;
        let entries = test_file.commands;

        let mut assert_returns_per_module = Vec::new();

        for entry in entries {
            match entry {
                CommandEntry::Module { filename, line } => {
                    assert_returns_per_module.push((parent_dir.join(filename), line, Vec::new()));
                }
                CommandEntry::AssertReturn {
                    action,
                    expected,
                    line,
                }
                | CommandEntry::Action {
                    action,
                    expected,
                    line,
                } => {
                    if let Some(function_name) = action.field {
                        let args = action.args.unwrap_or_default();

                        let args = args.iter().flat_map(parse_val).collect::<Vec<_>>();

                        let expected = expected.iter().flat_map(parse_val).collect::<Vec<_>>();
                        assert_returns_per_module
                            .last_mut()
                            .unwrap()
                            .2
                            .push(AssertCase {
                                function_name,
                                args,
                                expected,
                                _line: line,
                            });
                    }
                }
                CommandEntry::Other => {}
            }
        }

        Ok(assert_returns_per_module)
    }

    fn parse_val(val: &Val) -> Vec<u32> {
        match val.val_type.as_str() {
            "i32" | "f32" => vec![val.value.as_str().unwrap().parse::<u32>().unwrap()],
            "i64" | "f64" => {
                let v = val.value.as_str().unwrap().parse::<u64>().unwrap();
                vec![v as u32, (v >> 32) as u32]
            }
            "externref" => {
                let val = val.value.as_str().unwrap();
                if val == "null" {
                    NULL_REF.into()
                } else {
                    // use three bytes to be compatible with our `funcref`
                    // we don't care much about its representation, only
                    // that it is not a null reference.
                    vec![0, val.parse::<u32>().unwrap(), 1]
                }
            }
            "funcref" => {
                let val = val.value.as_str().unwrap();
                if val == "null" {
                    NULL_REF.into()
                } else {
                    panic!("Unexpected funcref value: {val}");
                }
            }
            _ => todo!(),
        }
    }
}
