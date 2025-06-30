mod block_tree;
mod blockless_dag;
mod dag;
pub mod flattening;
mod locals_data_flow;

use core::panic;
use std::{
    collections::{BTreeMap, BTreeSet, btree_map::Entry},
    marker::PhantomData,
    ops::RangeFrom,
    rc::Rc,
    vec,
};

use block_tree::BlockTree;
use dag::Dag;
use flattening::WriteOnceASM;
use itertools::Itertools;
use wasmparser::{
    CompositeInnerType, ElementItems, FuncValidatorAllocations, LocalsReader, MemoryType, Operator,
    Parser, Payload, RefType, TableInit, TypeRef, ValType, Validator, WasmFeatures,
};

use crate::loader::{
    blockless_dag::{BlocklessDag, BreakTarget},
    dag::ValueOrigin,
    flattening::settings::Settings,
};

pub use flattening::{func_idx_to_label, word_count_type};

#[derive(Debug, Clone)]
pub enum Global<'a> {
    Mutable(AllocatedVar),
    /// One of the *Const operators.
    Immutable(Operator<'a>),
}

#[derive(Debug, Clone, Copy)]
pub struct AllocatedVar {
    pub val_type: ValType,
    /// If it is a local or stack, this address is relative to the stack base.
    /// If it is a global, this address is absolute.
    pub address: u32,
}

/// WASM defined page size is 64 KiB.
pub const WASM_PAGE_SIZE: u32 = 65536;

/// If the table has no specified maximum size, we assign it a large default, in number of entries.
const DEFAULT_MAX_TABLE_SIZE: u32 = 4096;

/// Segment is not a WASM concept, but it is used to mean a region of memory
/// that is allocated for a WASM table or memory.
#[derive(Debug, Clone, Copy)]
pub struct Segment {
    /// The start address of the segment, in bytes.
    pub start: u32,
    /// The size of the segment, in bytes.
    pub size: u32,
}

#[derive(Debug, Clone, Copy)]
pub enum MemoryEntry {
    /// Actual value stored in memory word.
    Value(u32),
    /// Refers to the function address of a given function index.
    FuncAddr(u32),
    /// Refers to the function frame size of a given function index.
    FuncFrameSize(u32),
}

/// Helper struct to track unallocated memory.
/// This is used to allocate the memory for the tables and the globals.
struct MemoryAllocator {
    /// The address of the next free memory, in bytes.
    next_free: u32,
}

impl MemoryAllocator {
    fn new() -> Self {
        MemoryAllocator { next_free: 0 }
    }

    fn allocate_var(&mut self, val_type: ValType) -> AllocatedVar {
        let var = AllocatedVar {
            val_type,
            address: self.next_free,
        };
        self.next_free = self.next_free.checked_add(sz(val_type)).unwrap();
        var
    }

    fn allocate_segment(&mut self, size: u32) -> Segment {
        assert!(size % 4 == 0);
        let segment = Segment {
            start: self.next_free,
            size,
        };
        self.next_free = self.next_free.checked_add(size).unwrap();
        segment
    }

    fn remaining_space(&self) -> u32 {
        // The maximum size of the memory is 4 GiB, so we can use 32 bits to represent it.
        u32::MAX - self.next_free
    }
}

struct InitialMemory(BTreeMap<u32, MemoryEntry>);

impl InitialMemory {
    fn new() -> Self {
        InitialMemory(BTreeMap::new())
    }

    fn insert(&mut self, address: u32, entry: MemoryEntry) {
        if matches!(entry, MemoryEntry::Value(0)) {
            // We don't need to store 0 values, as they are the default.
            return;
        }
        self.0.insert(address, entry);
    }

    fn get(&self, address: u32) -> MemoryEntry {
        *self.0.get(&address).unwrap_or(&MemoryEntry::Value(0))
    }

    /// Insert up to 4 bytes of data at the given address.
    ///
    /// If there is an existing value at the address, the replaced bytes must be 0.
    fn insert_bytes(&mut self, address: u32, start_byte: u32, value: &[u8]) {
        let mut word = 0;
        let mut mask = 0;
        for (i, byte) in value.iter().take(4).enumerate() {
            let bit_offset = (start_byte + i as u32) * 8;
            word |= (*byte as u32) << bit_offset;
            mask |= 0xFF << bit_offset;
        }

        word <<= start_byte * 8;
        mask <<= start_byte * 8;

        match self.0.entry(address) {
            Entry::Vacant(entry) => {
                if word != 0 {
                    // We don't need to store 0 values, as they are the default.
                    entry.insert(MemoryEntry::Value(word));
                }
            }
            Entry::Occupied(mut entry) => {
                let MemoryEntry::Value(old_value) = entry.get() else {
                    panic!("Memory entry is not a value");
                };
                let new_value = (old_value & !mask) | word;
                if new_value == 0 {
                    entry.remove();
                } else {
                    entry.insert(MemoryEntry::Value(new_value));
                }
            }
        }
    }
}

/// The table entry high level layout.
struct FunctionRef<'a, S: Settings<'a>> {
    /// The unique type ID of the function type.
    type_id: u32,
    /// The function index.
    func_index: u32,
    settings: PhantomData<(&'a (), S)>,
}

impl<'a, S: Settings<'a>> FunctionRef<'a, S> {
    fn new(type_id: u32, func_index: u32) -> Self {
        FunctionRef {
            type_id,
            func_index,
            settings: PhantomData,
        }
    }
}

/// A function reference in the table is a 3-tuple of u32 values:
/// - The type ID of the function type.
/// - The function frame size, in words.
/// - The function address, which is a pointer to the function code.
///
/// If the architecture uses a different size for function pointers, it needs to be converted
/// to the correct size in the implementations of the instructions that use function references.
///
/// This struct is used to tell where, inside an entry, each of the values is stored.
impl<'a, S: Settings<'a>> FunctionRef<'a, S> {
    const TYPE_ID: usize = 0;
    const FUNC_FRAME_SIZE: usize = 1;
    const FUNC_ADDR: usize = 2;

    fn to_memory_entries(&self) -> Vec<MemoryEntry> {
        // If needed, this can be made to support non-power-of-two word sizes.
        // Which I doubt will ever be needed. People are not this crazy.
        assert!(S::bytes_per_word().is_power_of_two());

        let mut entries = Vec::with_capacity(Self::total_byte_size() as usize / 4);
        entries.push(MemoryEntry::Value(self.type_id));
        entries.extend(itertools::repeat_n(
            MemoryEntry::Value(0),
            Self::u32_padding(),
        ));
        entries.push(MemoryEntry::FuncFrameSize(self.func_index));
        entries.extend(itertools::repeat_n(
            MemoryEntry::Value(0),
            Self::u32_padding(),
        ));
        entries.push(MemoryEntry::FuncAddr(self.func_index));
        entries.extend(itertools::repeat_n(
            MemoryEntry::Value(0),
            Self::u32_padding(),
        ));
        entries
    }

    /// How many memory words of padding are needed after a u32 value.
    fn u32_padding() -> usize {
        let alignment = S::bytes_per_word().max(4);
        ((align(4, alignment) - 4) / 4) as usize
    }

    fn total_byte_size() -> u32 {
        let alignment = S::bytes_per_word().max(4);
        3 * align(4, alignment)
    }
}

const fn align(value: u32, power_of_two_alignment: u32) -> u32 {
    (value + power_of_two_alignment - 1) & !(power_of_two_alignment - 1)
}

#[derive(Debug, Clone)]
pub struct FuncType {
    /// Unique type identifier, used by indirect calls.
    ///
    /// We can't use type index directly, because there might be
    /// duplicated compatible types with different indices.
    pub unique_id: u32,
    pub ty: wasmparser::FuncType,
}

#[derive(Debug, Clone)]
pub struct CommonProgram<'a> {
    types: Vec<Rc<FuncType>>,
    func_types: Vec<u32>,
    table_types: Vec<RefType>,

    /// The module and name of the imported functions.
    ///
    /// Function idices overlaps with `functions` up to `imported_functions` length.
    pub imported_functions: Vec<(&'a str, &'a str)>,
    /// The start function, if any.
    pub start_function: Option<u32>,
    /// The exported functions.
    pub exported_functions: BTreeMap<u32, &'a str>,
    /// The initial memory, with the values to be set at startup.
    pub initial_memory: BTreeMap<u32, MemoryEntry>,
    /// The globals, in order of definition.
    pub globals: Vec<Global<'a>>,
    /// The memory segment, if any.
    pub memory: Option<Segment>,
    /// The tables, in order of definition.
    pub tables: Vec<Segment>,
    /// The special segments for table initialization.
    pub elem_segments: Vec<Segment>,
    /// The special segments for data initialization.
    pub data_segments: Vec<Segment>,
}

impl<'a> CommonProgram<'a> {
    fn get_type(&self, type_idx: u32) -> &FuncType {
        &self.types[type_idx as usize]
    }

    fn get_type_rc(&self, type_idx: u32) -> Rc<FuncType> {
        self.types[type_idx as usize].clone()
    }

    pub fn get_func_type(&self, func_idx: u32) -> &FuncType {
        self.get_type(self.func_types[func_idx as usize])
    }

    fn get_imported_func(&self, func_idx: u32) -> Option<(&'a str, &'a str)> {
        self.imported_functions.get(func_idx as usize).copied()
    }

    fn get_exported_func(&self, func_idx: u32) -> Option<&'a str> {
        self.exported_functions.get(&func_idx).copied()
    }

    /// Returns the memory segment information, allocating if needed.
    fn get_memory(
        &mut self,
        mem_allocator: &mut MemoryAllocator,
        initial_memory: &mut InitialMemory,
        mem_type: &Option<MemoryType>,
    ) -> Option<Segment> {
        let Some(mem_type) = mem_type else {
            return None;
        };

        if self.memory.is_none() {
            let maximum_size = mem_allocator
                .remaining_space()
                // From all the memory available, we reserve the 8 bytes needed
                // to store the size of the memory and its maximum size:
                .saturating_sub(8)
                / WASM_PAGE_SIZE;

            if maximum_size < mem_type.initial as u32 {
                panic!(
                    "Not enough address space available to allocate the initial memory plus the stack"
                );
            }

            let maximum_size = mem_type
                .maximum
                .map_or(maximum_size, |v| maximum_size.min(v as u32));

            let segment = mem_allocator.allocate_segment(maximum_size * WASM_PAGE_SIZE + 8);
            initial_memory.insert(segment.start, MemoryEntry::Value(mem_type.initial as u32));
            initial_memory.insert(segment.start + 4, MemoryEntry::Value(maximum_size));

            self.memory = Some(segment);
        }

        self.memory
    }
}

#[derive(Debug, Clone)]
pub struct Program<'a, S: Settings<'a>> {
    /// The settings used for the program.
    pub s: S,

    /// Non-generic part of the program, separated to avoid generic code bloat.
    pub c: CommonProgram<'a>,

    /// The functions defined in the module.
    ///
    /// Function idices overlaps with `imported_functions` up to its length.
    ///
    /// Indices `[0..imported_functions.len()]` refers to generated wrappers around the imported
    /// functions, which can be used for indirect calls, and indices [imported_functions.len()..]
    /// refers to the functions defined in the module.
    pub functions: Vec<WriteOnceASM<'a, S>>,
}

impl<'a, S: Settings<'a>> Program<'a, S> {
    fn eval_const_op(
        &self,
        val_type: ValType,
        op: &wasmparser::Operator<'a>,
    ) -> wasmparser::Result<Vec<MemoryEntry>> {
        Ok(match op {
            Operator::I32Const { value } => {
                assert_eq!(val_type, ValType::I32);
                vec![MemoryEntry::Value(*value as u32)]
            }
            Operator::I64Const { value } => {
                assert_eq!(val_type, ValType::I64);
                vec![
                    MemoryEntry::Value(*value as u32),
                    MemoryEntry::Value((value >> 32) as u32),
                ]
            }
            Operator::F32Const { value } => {
                assert_eq!(val_type, ValType::F32);
                vec![MemoryEntry::Value(value.bits())]
            }
            Operator::F64Const { value } => {
                assert_eq!(val_type, ValType::F64);
                let v: u64 = value.bits();
                vec![
                    MemoryEntry::Value(v as u32),
                    MemoryEntry::Value((v >> 32) as u32),
                ]
            }
            Operator::RefFunc { function_index } => {
                assert_eq!(val_type, ValType::Ref(RefType::FUNCREF));
                FunctionRef::<S>::new(
                    self.c.get_func_type(*function_index).unique_id,
                    *function_index,
                )
                .to_memory_entries()
            }
            Operator::RefNull { .. } => {
                assert!(matches!(val_type, ValType::Ref(_)));
                // Since (0, 0) is a valid function reference, lets use u32::MAX to represent null.
                vec![MemoryEntry::Value(u32::MAX), MemoryEntry::Value(u32::MAX)]
            }
            Operator::GlobalGet { global_index } => {
                let Global::Immutable(op) = &self.c.globals[*global_index as usize] else {
                    panic!("non-constant global used in const expression");
                };

                return self.eval_const_op(val_type, op);
            }
            op => panic!("Unsupported operator in const expr: {op:?}"),
        })
    }

    fn eval_const_expr(
        &self,
        val_type: ValType,
        expr: impl IntoIterator<Item = wasmparser::Result<wasmparser::Operator<'a>>>,
    ) -> wasmparser::Result<(Operator<'a>, Vec<MemoryEntry>)> {
        let mut iter = expr.into_iter();

        let op = iter.next().unwrap()?;
        let words = self.eval_const_op(val_type, &op)?;

        let end_op = iter.next().unwrap()?;
        assert_eq!(end_op, Operator::End);
        assert!(iter.next().is_none());

        Ok((op, words))
    }
}

/// Type size, in bytes
const fn sz(val_type: ValType) -> u32 {
    match val_type {
        ValType::I32 => 4,
        ValType::I64 => 8,
        ValType::F32 => 4,
        ValType::F64 => 8,
        ValType::V128 => 16,
        // References don't have a visible size in the WASM memory.
        ValType::Ref(_) => panic!("Cannot get size of reference type"),
    }
}

/// Arranges the bytes in little-endian words.
///
/// Alignment mod 4 is the byte offset of the first word.
fn pack_bytes_into_words(bytes: &[u8], mut alignment: u32) -> Vec<MemoryEntry> {
    let mut words = Vec::new();
    let mut value = 0;
    alignment %= 4;
    for byte in bytes.iter() {
        value |= (*byte as u32) << (alignment * 8);
        if alignment == 3 {
            words.push(MemoryEntry::Value(value));
            value = 0;
            alignment = 0;
        } else {
            alignment += 1;
        }
    }
    if bytes.len() % 4 != 0 {
        words.push(MemoryEntry::Value(value));
    }
    words
}

#[derive(Debug, Default)]
struct Statistics {
    /// Number of register copies saved by the "smart" register allocation.
    register_copies_saved: usize,
    /// Number of constants deduplicated in the DAG.
    constants_deduplicated: usize,
    /// Number of dangling nodes removed from the DAG.
    dangling_nodes_removed: usize,
    /// Number of block outputs removed from the DAG.
    block_outputs_removed: usize,
}

pub fn load_wasm<'a, S: Settings<'a>>(
    settings: S,
    wasm_file: &'a [u8],
) -> wasmparser::Result<Program<'a, S>> {
    let parser = Parser::new(0);

    let mut ctx = Program {
        c: CommonProgram {
            types: Vec::new(),
            func_types: Vec::new(),
            table_types: Vec::new(),

            imported_functions: Vec::new(),
            start_function: None,
            exported_functions: BTreeMap::new(),
            // This is left empty for most of this function, and will be filled just before returning.
            initial_memory: BTreeMap::new(),
            globals: Vec::new(),
            memory: None,
            tables: Vec::new(),
            elem_segments: Vec::new(),
            data_segments: Vec::new(),
        },

        s: settings,
        functions: Vec::new(),
    };

    // This is the memory layout of the program after all the elements have been allocated:
    // - all tables, in sequence, where each table contains:
    //   - the first word is the table size, in number of elements
    //   - the second word is the maximum size, in number of elements
    //   - then a sequence of entries of 2 words (references).
    // - all globals, in sequence
    // - all passive element segments, in sequence, where each segment is:
    //   - the first word is the segment size, in number of elements (this size is fixed)
    //   - a sequence of entries of 2 words (references).
    // - all passive data segments, in sequence, where each segment is:
    //   - the first word is the segment size, in bytes (this size is mostly fixed, but can be set to 0 on data.drop)
    //   - a sequence N words, where N is the minimum number of words to fit all bytes. Last word may be 0-padded.
    // - the WASM memory instance, where:
    //   - the first word is the size of the memory, in pages of 64 KiB
    //   - the second word is the maximum size of the memory, in pages of 64 KiB
    //   - then the memory byte array
    // - the WASM stack, that can grow to the maximum size of the memory
    let mut mem_type = None;
    let mut mem_allocator = MemoryAllocator::new();

    let mut initial_memory = InitialMemory::new();

    let mut label_gen = 0..;

    let mut stats = Statistics::default();

    let mut validator = Validator::new_with_features(WasmFeatures::WASM2);
    let mut validator_allocs = FuncValidatorAllocations::default();

    // The payloads are processed in the order they appear in the file, so each variable written
    // in one step is available in the next steps.
    let mut unsupported_feature_found = false;
    for payload in parser.parse_all(wasm_file) {
        match payload? {
            Payload::Version {
                num,
                encoding,
                range,
            } => {
                // This is the encoding version, we don't care about it besides validating.
                log::debug!("Binary encoding version: {num}");
                validator.version(num, encoding, &range)?;
            }
            Payload::TypeSection(section) => {
                log::debug!("Type Section found");
                validator.type_section(&section)?;

                let mut types = Vec::new();
                for rec_group in section {
                    let mut iter = rec_group?.into_types();
                    let ty = match (iter.next(), iter.next()) {
                        (Some(subtype), None) => match &subtype.composite_type.inner {
                            CompositeInnerType::Func(_) => match subtype.composite_type.inner {
                                CompositeInnerType::Func(f) => f,
                                _ => panic!("gc proposal not supported"),
                            },
                            _ => {
                                unsupported_feature_found = true;
                                log::error!("unsupported types from GC proposal found");
                                continue;
                            }
                        },
                        _ => {
                            // Apparently WebAssembly 3.0 is much more complicated, and has complex
                            // type definitions, and garbage collector, and exceptions. We should probably
                            // stick to the 2.0 version for Powdr.
                            unsupported_feature_found = true;
                            log::error!("unsupported types from GC proposal found");
                            continue;
                        }
                    };
                    let type_idx = types.len() as u32;
                    types.push((type_idx, ty));
                    log::debug!("Type read: {:?}", types.last().unwrap());
                }

                // Deduplicate the types
                let num_types = types.len();
                if num_types > 0 {
                    types.sort_by(|a, b| a.1.cmp(&b.1));
                    let mut types = types.into_iter();

                    let mut initial = Vec::with_capacity(num_types);
                    let (unique_id, ty) = types.next().unwrap();
                    initial.push((unique_id, Rc::new(FuncType { unique_id, ty })));

                    // I tried doing this with itertools' `chunk_by()`, but lifetimes didn't let me.
                    let mut unique_types = types.fold(initial, |mut acc, (type_idx, ty)| {
                        let (_, last_ty) = acc.last().unwrap();
                        if ty == last_ty.ty {
                            acc.push((type_idx, last_ty.clone()));
                        } else {
                            acc.push((
                                type_idx,
                                Rc::new(FuncType {
                                    unique_id: type_idx,
                                    ty,
                                }),
                            ));
                        }
                        acc
                    });
                    // There is an unsafe + MaybeUninit version of this that doesn't require sorting...
                    unique_types.sort_unstable_by_key(|(type_idx, _)| *type_idx);
                    ctx.c.types = unique_types.into_iter().map(|(_, ty)| ty).collect();
                    assert_eq!(ctx.c.types.len(), num_types);
                }
            }
            Payload::ImportSection(section) => {
                log::debug!("Import Section found");
                validator.import_section(&section)?;

                // TODO: we could implement module load and cross module dependencies,
                // but this is not a very used feature in WASM and modules are usually
                // self-contained.
                //
                // For now, the imports only deal with user provided functions.
                for import in section {
                    let import = import?;
                    // Save the imported thing if it is a function.
                    // We actually just support function imports, so we ignore the rest.
                    if let TypeRef::Func(type_idx) = import.ty {
                        log::debug!("Imported syscall: {}.{}", import.module, import.name);

                        let func_idx = ctx.c.imported_functions.len() as u32;
                        ctx.c.func_types.push(type_idx);
                        ctx.c.imported_functions.push((import.module, import.name));

                        let (wrapper_dag, copies_saved) =
                            generate_imported_func_wrapper::<S>(&ctx, &mut label_gen, func_idx);
                        stats.register_copies_saved += copies_saved;
                        ctx.functions.push(wrapper_dag);
                    } else if import.module == "spectest" {
                        // To run the tests, the runtime must provide a few basic imports
                        // of the `spectest` module.
                        //
                        // The definition is here:
                        // https://github.com/WebAssembly/spec/blob/main/interpreter/README.md#spectest-host-module
                        match import.ty {
                            TypeRef::Memory(mut mtype) if import.name == "memory" => {
                                // The spectest memory is always 2 pages, so we set the maximum to 2.
                                mtype.maximum = Some(2);
                                mtype.initial = 1;
                                log::debug!("spectest.memory imported: {mtype:?}");
                                mem_type = Some(mtype);
                            }
                            TypeRef::Global(gtype) => {
                                assert!(!gtype.mutable);
                                let value = match import.name {
                                    "global_i32" => Operator::I32Const { value: 666 },
                                    "global_i64" => Operator::I64Const { value: 666 },
                                    "global_f32" => Operator::F32Const {
                                        value: 666.6.into(),
                                    },
                                    "global_f64" => Operator::F64Const {
                                        value: 666.6.into(),
                                    },
                                    _ => {
                                        log::error!(
                                            "Unsupported spectest import: {}.{} ({:?})",
                                            import.module,
                                            import.name,
                                            import.ty
                                        );
                                        unsupported_feature_found = true;
                                        continue;
                                    }
                                };
                                ctx.c.globals.push(Global::Immutable(value));
                            }
                            _ => {
                                log::error!(
                                    "Unsupported spectest import: {}.{} ({:?})",
                                    import.module,
                                    import.name,
                                    import.ty
                                );
                                unsupported_feature_found = true;
                            }
                        }
                    } else {
                        log::error!(
                            "Unsupported import: {}.{} ({:?})",
                            import.module,
                            import.name,
                            import.ty
                        );
                        unsupported_feature_found = true;
                    }
                }
            }
            Payload::FunctionSection(section) => {
                log::debug!("Function Section found");
                validator.function_section(&section)?;

                for type_idx in section {
                    let type_idx = type_idx?;
                    let func_idx = ctx.c.func_types.len() as u32;
                    ctx.c.func_types.push(type_idx);
                    log::debug!(
                        "Type of function {func_idx}: {type_idx} ({:?})",
                        ctx.c.get_type(type_idx)
                    );
                }
            }
            Payload::TableSection(section) => {
                log::debug!("Table Section found");
                validator.table_section(&section)?;

                for table in section {
                    let table = table?;
                    if (!table.ty.element_type.is_extern_ref()
                        && !table.ty.element_type.is_func_ref())
                        || table.ty.table64
                        || table.ty.shared
                    {
                        unsupported_feature_found = true;
                        log::error!("Found table with unsupported properties",);
                        continue;
                    }

                    if !matches!(table.init, TableInit::RefNull) {
                        unsupported_feature_found = true;
                        log::error!("Table initialization is not supported");
                        continue;
                    }

                    log::debug!(
                        "Table defined. Initial size: {}, maximum size: {:?}",
                        table.ty.initial,
                        table.ty.maximum
                    );

                    let max_entries = table
                        .ty
                        .maximum
                        .map(|v| v as u32)
                        .unwrap_or(DEFAULT_MAX_TABLE_SIZE);

                    // We include two extra words for the table size and maximum size
                    let segment = mem_allocator
                        .allocate_segment(max_entries * FunctionRef::<S>::total_byte_size() + 8);

                    // Store the table size and maximum size in the initial memory
                    initial_memory
                        .insert(segment.start, MemoryEntry::Value(table.ty.initial as u32));
                    initial_memory.insert(segment.start + 4, MemoryEntry::Value(max_entries));

                    ctx.c.tables.push(segment);
                    ctx.c.table_types.push(table.ty.element_type);
                }
            }
            Payload::MemorySection(section) => {
                log::debug!("Memory Section found");
                validator.memory_section(&section)?;

                for mem in section {
                    let mem = mem?;

                    if ctx.c.memory.is_some() {
                        unsupported_feature_found = true;
                        log::error!("Multiple memories are not supported");
                        break;
                    }

                    if mem.memory64 || mem.shared || mem.page_size_log2.is_some() {
                        unsupported_feature_found = true;
                        log::error!("Found memory with unsupported properties");
                        continue;
                    }

                    log::debug!(
                        "Memory defined. Initial size: {} pages, maximum size: {:?} pages",
                        mem.initial,
                        mem.maximum
                    );

                    // Lets delay the actual memory allocation to after the globals are allocated.
                    mem_type = Some(mem);
                }
            }
            Payload::TagSection(s) => {
                // I don't think this is part of WASM 2.0, but we give it to the validator,
                // only to error out in case this is matched.
                validator.tag_section(&s)?;
            }
            Payload::GlobalSection(section) => {
                log::debug!("Global Section found");
                validator.global_section(&section)?;

                for global in section {
                    let global = global?;
                    let ty = global.ty.content_type;
                    let (const_op, words) =
                        ctx.eval_const_expr(ty, global.init_expr.get_operators_reader())?;

                    log::debug!("Global variable {} has type {:?}", ctx.c.globals.len(), ty);

                    let global = if global.ty.mutable {
                        // Initialize the global variables
                        let var = mem_allocator.allocate_var(ty);
                        for (idx, word) in words.into_iter().enumerate() {
                            initial_memory.insert(var.address + 4 * idx as u32, word);
                        }
                        Global::Mutable(var)
                    } else {
                        // Immutable globals are initialized with a constant expression.
                        // We store the operator in the global, so it can be evaluated later.
                        Global::Immutable(const_op)
                    };
                    ctx.c.globals.push(global);
                }
            }
            Payload::ExportSection(section_limited) => {
                log::debug!("Export Section found");
                validator.export_section(&section_limited)?;

                for export in section_limited {
                    let export = export?;
                    log::debug!(
                        "Exported entity: {}, kind {:?}, index: {}",
                        export.name,
                        export.kind,
                        export.index
                    );

                    match export.kind {
                        wasmparser::ExternalKind::Func => {
                            ctx.c.exported_functions.insert(export.index, export.name);
                        }
                        _ => {
                            // We don't have anything to do with other kinds of exports.
                        }
                    }
                }
            }
            Payload::StartSection { func, range } => {
                log::debug!("Start Section found. Start function: {func}");
                validator.start_section(func, &range)?;

                ctx.c.start_function = Some(func);
            }
            Payload::ElementSection(section) => {
                log::debug!("Element Section found");
                validator.element_section(&section)?;

                for elem_segment in section {
                    let elem_segment = elem_segment?;

                    // Get all the values in the segment
                    let mut values = Vec::new();
                    match elem_segment.items {
                        ElementItems::Functions(section) => {
                            for idx in section {
                                let idx = idx?;
                                values.extend(
                                    FunctionRef::<S>::new(ctx.c.get_func_type(idx).unique_id, idx)
                                        .to_memory_entries(),
                                );
                            }
                        }
                        ElementItems::Expressions(ref_type, section) => {
                            for elem in section {
                                let (_, val) = ctx.eval_const_expr(
                                    ValType::Ref(ref_type),
                                    elem?.get_operators_reader(),
                                )?;
                                values.extend(val);
                            }
                        }
                    };
                    let num_elems = values.len() as u32 / (FunctionRef::<S>::total_byte_size() / 4);

                    // Decide what to do with the values
                    match elem_segment.kind {
                        wasmparser::ElementKind::Passive => {
                            // This is stored as a memory segment to be used by table.init instruction

                            log::debug!(
                                "Passive table segment found. Number of elements: {num_elems}"
                            );

                            // We include one extra word: the segment size
                            let segment = mem_allocator.allocate_segment(
                                4 + num_elems * FunctionRef::<S>::total_byte_size(),
                            );

                            // Store the segment size in the initial memory
                            initial_memory.insert(segment.start, MemoryEntry::Value(num_elems));

                            // Store the values in the initial memory
                            for (idx, word) in values.into_iter().enumerate() {
                                initial_memory.insert(segment.start + 4 * (idx as u32 + 1), word);
                            }

                            // Store the segment in the context
                            ctx.c.elem_segments.push(segment);
                        }
                        wasmparser::ElementKind::Active {
                            table_index,
                            offset_expr,
                        } => {
                            // This is used to statically initialize the table. We can set the values on the table directly.

                            // I am assuming the table index of 0 if not provided, as hinted by the WASM binary spec.
                            let idx = table_index.unwrap_or(0);
                            let table = &ctx.c.tables[idx as usize];

                            let &[MemoryEntry::Value(offset)] = ctx
                                .eval_const_expr(ValType::I32, offset_expr.get_operators_reader())?
                                .1
                                .as_slice()
                            else {
                                panic!("Offset is not a u32 value");
                            };

                            log::debug!(
                                "Active table segment found. Table index: {idx}, offset: {offset}, number of elements: {num_elems}"
                            );

                            let MemoryEntry::Value(table_size) = initial_memory.get(table.start)
                            else {
                                panic!("Table size is a label");
                            };
                            assert!(offset + num_elems <= table_size);

                            let mut byte_offset =
                                table.start + 8 + offset * FunctionRef::<S>::total_byte_size();
                            for value in values {
                                initial_memory.insert(byte_offset, value);
                                byte_offset += 4;
                            }
                            assert!(byte_offset <= table.start + table.size);
                        }
                        wasmparser::ElementKind::Declared => {
                            // Declarative elements are informational, we don't need to do anything
                        }
                    }
                }
            }
            Payload::DataCountSection { count, range } => {
                // This is used only by the static validator.
                log::debug!("Data Count Section found. Count: {count}");
                validator.data_count_section(count, &range)?;
            }
            Payload::CodeSectionStart { count, range, .. } => {
                log::debug!("Code Section Start found. Count: {count}");
                validator.code_section_start(&range)?;

                assert_eq!(
                    ctx.c.imported_functions.len() + count as usize,
                    ctx.c.func_types.len()
                );
            }
            Payload::CodeSectionEntry(function) => {
                // By the time we get here, the ctx will be mostly complete,
                // because all previous sections have been processed.

                let func_idx = ctx.functions.len() as u32;
                log::debug!("Code Section Entry found, function {func_idx}");
                let mut func_validator = validator
                    .code_section_entry(&function)?
                    .into_validator(validator_allocs);
                func_validator.validate(&function)?;
                validator_allocs = func_validator.into_allocations();

                let func_type = ctx.c.get_func_type(func_idx);
                let locals_types = read_locals(func_type, function.get_locals_reader()?)?;

                // Loads the function to memory in the BlockTree format.
                let block_tree =
                    BlockTree::load_function(&ctx.c, function.get_operators_reader()?)?;

                // Expose the reads and writes to locals inside blocks as inputs and outputs.
                let lifted_blocks = locals_data_flow::lift_data_flow(block_tree)?;

                // Build the DAG
                let mut dag = Dag::new(&ctx.c, &func_type.ty, &locals_types, lifted_blocks)?;

                // Optimization pass: deduplicate const definitions in the DAG.
                stats.constants_deduplicated += dag::const_dedup::deduplicate_constants(&mut dag);

                loop {
                    // Optimization pass: remove unused const nodes.
                    let pass_stats = dag::dangling_removal::clean_dangling_outputs(&mut dag);
                    stats.dangling_nodes_removed += pass_stats.removed_nodes;
                    stats.block_outputs_removed += pass_stats.removed_block_outputs;

                    if pass_stats.removed_nodes == 0 && pass_stats.removed_block_outputs == 0 {
                        break;
                    }
                }

                let blockless_dag = blockless_dag::BlocklessDag::new(dag, &mut label_gen);

                let (definition, copies_saved) =
                    flattening::flatten_dag::<S>(&ctx, &mut label_gen, blockless_dag, func_idx);
                stats.register_copies_saved += copies_saved;

                /*println!("Function: {func_idx}");
                for d in definition.directives.iter() {
                    println!("{d}");
                }*/

                ctx.functions.push(definition);
            }
            Payload::DataSection(section) => {
                log::debug!("Data Section found");
                validator.data_section(&section)?;

                for data_segment in section {
                    let data_segment = data_segment?;

                    match data_segment.kind {
                        wasmparser::DataKind::Passive => {
                            // This is stored as a memory segment to be used by memory.init instruction

                            // We include one extra word for the segment size
                            let byte_count = data_segment.data.len() as u32;
                            let segment = mem_allocator.allocate_segment(byte_count + 4);

                            // Store the segment size in the initial memory
                            initial_memory.insert(segment.start, MemoryEntry::Value(byte_count));

                            // Store the values in the initial memory
                            let values = pack_bytes_into_words(data_segment.data, 0);
                            for (idx, word) in values.into_iter().enumerate() {
                                initial_memory.insert(segment.start + 4 * (idx as u32 + 1), word);
                            }

                            // Store the segment in the context
                            ctx.c.data_segments.push(segment);
                        }
                        wasmparser::DataKind::Active {
                            memory_index,
                            offset_expr,
                        } => {
                            // This is used to statically initialize the memory. We can set the values on the memory directly.

                            if memory_index != 0 {
                                unsupported_feature_found = true;
                                log::error!("Found data segment with memory index other than 0");
                                continue;
                            }

                            let Some(memory) = ctx.c.get_memory(
                                &mut mem_allocator,
                                &mut initial_memory,
                                &mem_type,
                            ) else {
                                if !data_segment.data.is_empty() {
                                    unreachable!("Data segment but no memory defined");
                                }
                                continue;
                            };

                            let &[MemoryEntry::Value(offset)] = ctx
                                .eval_const_expr(ValType::I32, offset_expr.get_operators_reader())?
                                .1
                                .as_slice()
                            else {
                                panic!("Offset is not a u32 value");
                            };

                            let MemoryEntry::Value(mem_size) = initial_memory.get(memory.start)
                            else {
                                panic!("Memory size is a label");
                            };
                            let mem_size = mem_size * WASM_PAGE_SIZE;
                            assert!(offset + data_segment.data.len() as u32 <= mem_size);

                            let mut byte_offset = memory.start + 8 + offset;
                            let mut data = data_segment.data;

                            // If misaligned, handle the first word separately.
                            let alignment = byte_offset % 4;
                            if alignment != 0 {
                                byte_offset -= alignment;

                                let first_word;
                                (first_word, data) =
                                    data.split_at(data.len().min(4 - alignment as usize));
                                initial_memory.insert_bytes(byte_offset, alignment, first_word);
                                byte_offset += 4;
                            }

                            // Split the last word to be handled separately, if not a full word.
                            let last_word_len = data.len() % 4;
                            let last_word;
                            (data, last_word) = data.split_at(data.len() - last_word_len);

                            // General case, for the word aligned middle:
                            let values = pack_bytes_into_words(data, 0).into_iter();
                            for word in values {
                                initial_memory.insert(byte_offset, word);
                                byte_offset += 4;
                            }

                            // Insert the misaligned last word, if any.
                            if !last_word.is_empty() {
                                initial_memory.insert_bytes(byte_offset, 0, last_word);
                            }
                        }
                    }
                }
            }
            Payload::CustomSection(_) => {
                // TODO: read function names and debug information
                // There is no validation here.
            }
            Payload::UnknownSection { id, range, .. } => {
                // This is also a section we don't support, and is matched
                // only so validator can error out.
                validator.unknown_section(id, &range)?
            }
            Payload::End(offset) => {
                log::debug!("End of the module");
                validator.end(offset)?;
            }

            unsupported_section => {
                unsupported_feature_found = true;
                log::error!("Unsupported section found: {unsupported_section:?}");
            }
        }
    }

    let _ = ctx
        .c
        .get_memory(&mut mem_allocator, &mut initial_memory, &mem_type);

    assert!(
        !unsupported_feature_found,
        "Only WebAssembly Release 2.0 is supported"
    );

    ctx.c.initial_memory = initial_memory.0;

    log::info!(
        "WASM module loaded successfully loaded with {} functions!\nOptimization statistics:\n - {} register copies saved\n - {} constants deduplicated\n - {} dangling nodes removed\n - {} block outputs removed",
        ctx.functions.len(),
        stats.register_copies_saved,
        stats.constants_deduplicated,
        stats.dangling_nodes_removed,
        stats.block_outputs_removed
    );

    Ok(ctx)
}

/// Generates a wrapper function for an imported function.
fn generate_imported_func_wrapper<'a, S: Settings<'a>>(
    ctx: &Program<'a, S>,
    label_gen: &mut RangeFrom<u32>,
    function_idx: u32,
) -> (WriteOnceASM<'a, S>, usize) {
    let func_type = &ctx.c.get_func_type(function_idx).ty;

    // A very simple DAG that just calls the imported function.
    let dag = BlocklessDag {
        nodes: vec![
            blockless_dag::Node {
                operation: blockless_dag::Operation::Inputs,
                inputs: Vec::new(),
                output_types: func_type.params().to_vec(),
            },
            blockless_dag::Node {
                operation: blockless_dag::Operation::WASMOp(Operator::Call {
                    function_index: function_idx,
                }),
                inputs: (0..func_type.params().len() as u32)
                    .map(|i| ValueOrigin {
                        node: 0,
                        output_idx: i,
                    })
                    .collect(),
                output_types: func_type.results().to_vec(),
            },
            blockless_dag::Node {
                operation: blockless_dag::Operation::Br(BreakTarget {
                    depth: 0,
                    kind: blockless_dag::TargetType::FunctionOrLoop,
                }),
                inputs: (0..func_type.results().len() as u32)
                    .map(|i| ValueOrigin {
                        node: 1,
                        output_idx: i,
                    })
                    .collect(),
                output_types: Vec::new(),
            },
        ],
    };

    // Flatten the DAG into an assembly-like definition.
    // This will not turn into an infinite recursion because a Call
    // to an imported function if flattened into an ImportedCall.
    flattening::flatten_dag::<S>(ctx, label_gen, dag, function_idx)
}

/// Reads the function arguments and the explicit locals declaration.
fn read_locals<'a>(
    func_type: &'a FuncType,
    locals_reader: LocalsReader<'a>,
) -> wasmparser::Result<Vec<ValType>> {
    // The first locals are the function arguments.
    let mut local_types = func_type.ty.params().iter().copied().collect_vec();

    // The rest of the locals are explicitly defined local variables.
    for local in locals_reader {
        let (count, val_type) = local?;
        local_types.extend((0..count).map(|_| val_type));
    }

    Ok(local_types)
}

#[derive(Debug)]
pub enum Instruction<'a> {
    WASMOp(Operator<'a>),
    /// BrTable needs to be transformed, so we can't use the original
    /// Operator::BrTable.
    BrTable {
        targets: Vec<u32>,
    },
    /// BrIfZero is the the complementary to Operator::BrIf. I've added it
    /// because there is a small optimization that can be done when emmiting
    /// an if without an else.
    BrIfZero {
        relative_depth: u32,
    },
}

#[derive(Debug)]
pub enum BlockKind {
    Block,
    Loop,
}

#[derive(Debug)]
pub struct Block<'a> {
    block_kind: BlockKind,
    interface_type: Rc<FuncType>,
    elements: Vec<Element<'a>>,

    input_locals: BTreeSet<u32>,
    output_locals: BTreeSet<u32>,

    // Carried locals are a subset of the inputs that must be carried over to any breaks and output.
    // This is used when calculating locals data flow of loops: if a previous iteration changed some
    // local, the new value must be carried through all the breaks and output in the future iterations.
    carried_locals: BTreeSet<u32>,
}

#[derive(Debug)]
pub enum Element<'a> {
    Ins(Instruction<'a>),
    Block(Block<'a>),
}

impl<'a> From<Instruction<'a>> for Element<'a> {
    fn from(instruction: Instruction<'a>) -> Self {
        Element::Ins(instruction)
    }
}

impl<'a> From<Block<'a>> for Element<'a> {
    fn from(block: Block<'a>) -> Self {
        Element::Block(block)
    }
}
