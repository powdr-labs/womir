use std::{
    collections::{HashMap, HashSet, VecDeque},
    ops::AddAssign,
};

use itertools::Itertools;
use wasmparser::Operator as Op;

use crate::loader::{
    BlockKind,
    dag::{Dag, Node, Operation, ValueOrigin},
};

#[derive(Default, Debug)]
pub struct Statistics {
    pub removed_nodes: usize,
    pub removed_block_outputs: usize,
    // We don't track removed block inputs because they have no visible effect
    // on the generated code. They may, however, help remove more nodes, which
    // is already counted in `removed_nodes`.
}

impl AddAssign for Statistics {
    fn add_assign(&mut self, other: Self) {
        self.removed_nodes += other.removed_nodes;
        self.removed_block_outputs += other.removed_block_outputs;
    }
}

struct StackElement {
    sorted_removed_outputs: Vec<u32>,
}

struct OffsetMap<K: Ord, V: PartialEq + Eq> {
    default: V,
    counter: V,
    /// Holds the (index, value), sorted by index for binary search.
    map: Vec<(K, V)>,
}

impl<K: Ord + PartialEq + Eq, V: Copy + PartialEq + Eq + AddAssign<V> + From<u8>> OffsetMap<K, V> {
    fn new(default: V) -> Self {
        Self {
            default,
            counter: default,
            map: Vec::new(),
        }
    }

    fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    fn append(&mut self, index: K) {
        if let Some((k, _)) = self.map.last() {
            // The keys must be in ascending order.
            assert!(index >= *k);
        }

        self.counter += 1.into();
        self.map.push((index, self.counter));
    }

    fn get(&self, index: &K) -> &V {
        match self.map.binary_search_by(|(i, _)| i.cmp(index)) {
            Ok(idx) => &self.map[idx].1,
            Err(idx) => {
                if idx == 0 {
                    &self.default
                } else {
                    &self.map[idx - 1].1
                }
            }
        }
    }
}

fn _print_nodes(indent: usize, nodes: &[Node<'_>]) {
    let spaces = " ".repeat(indent);
    for (node_idx, node) in nodes.iter().enumerate() {
        if let Operation::Block { sub_dag, .. } = &node.operation {
            println!(
                "{spaces}{node_idx:4}: {} --",
                node.inputs
                    .iter()
                    .map(|o| format!("({}, {})", o.node, o.output_idx))
                    .format(", "),
            );
            _print_nodes(indent + 2, &sub_dag.nodes);
            println!(
                "{spaces}{node_idx:4}: --> {}",
                (0..node.output_types.len())
                    .map(|i| format!("({}, {})", node_idx, i))
                    .format(", ")
            );
        } else {
            println!(
                "{spaces}{node_idx:4}: {} -> {}",
                node.inputs
                    .iter()
                    .map(|o| format!("({}, {})", o.node, o.output_idx))
                    .format(", "),
                (0..node.output_types.len())
                    .map(|i| format!("({}, {})", node_idx, i))
                    .format(", ")
            );
        }
    }
}

/// This optimization pass detects outputs that are not used, and removes the
/// nodes that produce them, if they don't have side effects.
///
/// Returns the new DAG and the number of removed nodes.
pub fn clean_dangling_outputs(dag: &mut Dag) -> Statistics {
    //println!("\nBefore dangling removal:");
    //_print_nodes(0, &dag.nodes);

    // We don't remove anything from the top-level function output.
    let mut ctrl_stack = VecDeque::from([StackElement {
        sorted_removed_outputs: Vec::new(),
    }]);

    // We can't change its inputs, either.
    let (_, stats) = recursive_removal(&mut dag.nodes, &mut ctrl_stack, false);

    //println!("\nAfter dangling removal:");
    //print_nodes(0, &dag.nodes);

    stats
}

fn recursive_removal(
    nodes: &mut Vec<Node<'_>>,
    ctrl_stack: &mut VecDeque<StackElement>,
    remove_inputs: bool,
) -> (Vec<u32>, Statistics) {
    let mut stats = Statistics::default();

    // Some nodes outputs may be removed (in case of blocks or the inputs node).
    // This keeps track of what nodes had their outputs removed, so we can adjust
    // the inputs of subsequent nodes.
    let mut nodes_outputs_offsets = HashMap::new();

    // The first pass happens bottom up, and just detects which nodes can be removed.
    let mut used_outputs = HashSet::new();
    let to_be_removed = nodes
        .iter_mut()
        .enumerate()
        .rev()
        .filter_map(|(node_idx, node)| {
            let (bl_stats, outputs_offset) =
                recurse_into_block(node_idx, node, ctrl_stack, &used_outputs);
            stats += bl_stats;
            if !outputs_offset.is_empty() {
                nodes_outputs_offsets.insert(node_idx, outputs_offset);
            }

            let to_be_removed = !may_have_side_effect(node)
                && (0..node.output_types.len()).all(|output_idx| {
                    !used_outputs.contains(&ValueOrigin::new(node_idx, output_idx as u32))
                });

            if !to_be_removed {
                // If the node is not to be removed, mark its inputs as used.
                for node in node.inputs.iter() {
                    used_outputs.insert(*node);
                }
                None
            } else {
                Some(node_idx)
            }
        })
        .collect_vec();
    stats.removed_nodes += to_be_removed.len();

    // If requested, use the used_outputs to remove inputs that are no longer needed.
    let mut removed_inputs = Vec::new();
    if remove_inputs {
        let inputs = &mut nodes[0];
        assert!(matches!(inputs.operation, Operation::Inputs { .. }));

        let mut output_idx = 0u32..;
        let mut offset_map = OffsetMap::new(0);
        inputs.output_types.retain(|_| {
            let origin = ValueOrigin::new(0, output_idx.next().unwrap());
            if used_outputs.contains(&origin) {
                true
            } else {
                removed_inputs.push(origin.output_idx);
                offset_map.append(origin.output_idx);
                false
            }
        });

        nodes_outputs_offsets.insert(0, offset_map);
    }

    // The second pass happens top down, and actually removes the nodes.
    let mut offset_map = OffsetMap::new(0);
    let mut to_be_removed = to_be_removed.into_iter().rev().peekable();
    let mut node_idx = 0usize..;
    nodes.retain_mut(|node| {
        let node_idx = node_idx.next();
        if to_be_removed.peek() == node_idx.as_ref() {
            // Remove the node if it is in the to-be-removed list.
            to_be_removed.next();
            offset_map.append(node_idx.unwrap());
            false
        } else {
            // Fix the inputs to breaks, that might have changed.
            fix_breaks(node, ctrl_stack);

            // Fix the node index for all the inputs of a node that is not being removed.
            for input in node.inputs.iter_mut() {
                // If this refers to a node whose output has been removed, we need to remap it.
                if let Some(offset_map) = nodes_outputs_offsets.get(&input.node) {
                    input.output_idx -= offset_map.get(&input.output_idx);
                }

                input.node -= offset_map.get(&input.node);
            }
            true
        }
    });

    (removed_inputs, stats)
}

/// Apply the dangling removal recursivelly to a block node.
fn recurse_into_block(
    node_idx: usize,
    node: &mut Node,
    ctrl_stack: &mut VecDeque<StackElement>,
    used_outputs: &HashSet<ValueOrigin>,
) -> (Statistics, OffsetMap<u32, u32>) {
    if let Operation::Block { kind, sub_dag } = &mut node.operation {
        // We need to figure out which outputs of the block are not used, and remove them.
        let sorted_removed_outputs = (0..node.output_types.len() as u32)
            .filter(|output_idx| !used_outputs.contains(&ValueOrigin::new(node_idx, *output_idx)))
            .collect_vec();

        // It is too complicated to mess with loops inputs, so we keep them as is.
        // TODO: handle loop inputs properly. Probably useless if the WASM is already optimized.
        let remove_inputs = match kind {
            BlockKind::Loop => false,
            BlockKind::Block => true,
        };

        ctrl_stack.push_front(StackElement {
            sorted_removed_outputs,
        });
        let (removed_inputs, mut stats) =
            recursive_removal(&mut sub_dag.nodes, ctrl_stack, remove_inputs);
        let stack_elem = ctrl_stack.pop_front().unwrap();

        remove_indices_from_vec(&mut node.inputs, &removed_inputs);
        remove_indices_from_vec(&mut node.output_types, &stack_elem.sorted_removed_outputs);
        stats.removed_block_outputs += stack_elem.sorted_removed_outputs.len();

        let mut offset_map = OffsetMap::new(0);
        for removed in stack_elem.sorted_removed_outputs {
            offset_map.append(removed);
        }

        (stats, offset_map)
    } else {
        (Statistics::default(), OffsetMap::new(0))
    }
}

/// Fix breaks to blocks that had their outputs removed.
fn fix_breaks(node: &mut Node, ctrl_stack: &mut VecDeque<StackElement>) {
    match &mut node.operation {
        Operation::WASMOp(Op::Br { relative_depth })
        | Operation::WASMOp(Op::BrIf { relative_depth })
        | Operation::BrIfZero { relative_depth } => {
            // BrIf and BrIfZero have one more input: the condition.
            // But since it is the last one, it won't be affected by the removal.
            let idx_to_remove = &ctrl_stack[*relative_depth as usize].sorted_removed_outputs;
            remove_indices_from_vec(&mut node.inputs, idx_to_remove);
        }
        Operation::BrTable { targets } => {
            let mut is_input_still_used = vec![false; node.inputs.len()];
            is_input_still_used[node.inputs.len() - 1] = true; // Keep the selector!

            // Remove the inputs for each target individually.
            for target in targets.iter_mut() {
                let idx_to_remove =
                    &ctrl_stack[target.relative_depth as usize].sorted_removed_outputs;
                remove_indices_from_vec(&mut target.input_permutation, idx_to_remove);

                // Mark the br_table inputs that are still used.
                for input_idx in target.input_permutation.iter() {
                    is_input_still_used[*input_idx as usize] = true;
                }
            }

            // Remove the inputs that are not used in any target.
            let mut offset_map = OffsetMap::new(0);
            let mut is_input_still_used = (0u32..).zip(is_input_still_used);
            node.inputs.retain(|_| {
                let (input_idx, is_used) = is_input_still_used.next().unwrap();
                if is_used {
                    // If the input is still used, keep it.
                    true
                } else {
                    // If the input is not used, remove it.
                    offset_map.append(input_idx);
                    false
                }
            });

            // Fix the input indices in the targets' input permutations.
            if !offset_map.is_empty() {
                for target in targets.iter_mut() {
                    for input_idx in target.input_permutation.iter_mut() {
                        *input_idx -= offset_map.get(input_idx);
                    }
                }
            }
        }
        _ => (/* Not a break operation, nothing to do */),
    }
}

fn remove_indices_from_vec<T>(vec: &mut Vec<T>, sorted_ids: &[u32]) {
    let mut sorted_ids = sorted_ids.iter().cloned().peekable();

    // We start the removal from the first index to be removed,
    // cutting the iteration short.
    let Some(initial_idx) = sorted_ids.next() else {
        return;
    };

    let mut dest = initial_idx as usize;
    for src in dest + 1..vec.len() {
        if sorted_ids.peek() == Some(&(src as u32)) {
            // If the current index is in the list of indices to be removed, skip it.
            sorted_ids.next();
        } else {
            // Otherwise, swap the value to the destination index.
            vec.swap(dest, src);
            dest += 1;
        }
    }
    // All the unused elements are at the end of the vector.
    vec.truncate(dest);
}

/// Checks if a node has side effects
fn may_have_side_effect(node: &Node) -> bool {
    if let Operation::WASMOp(
        // Constants are pure.
        Op::I32Const { .. }
        | Op::I64Const { .. }
        | Op::F32Const { .. }
        | Op::F64Const { .. }
        | Op::V128Const { .. }

        // Numeric operations are pure.
        | Op::I32Eqz
        | Op::I32Eq
        | Op::I32Ne
        | Op::I32LtS
        | Op::I32LtU
        | Op::I32GtS
        | Op::I32GtU
        | Op::I32LeS
        | Op::I32LeU
        | Op::I32GeS
        | Op::I32GeU
        | Op::I64Eqz
        | Op::I64Eq
        | Op::I64Ne
        | Op::I64LtS
        | Op::I64LtU
        | Op::I64GtS
        | Op::I64GtU
        | Op::I64LeS
        | Op::I64LeU
        | Op::I64GeS
        | Op::I64GeU
        | Op::F32Eq
        | Op::F32Ne
        | Op::F32Lt
        | Op::F32Gt
        | Op::F32Le
        | Op::F32Ge
        | Op::F64Eq
        | Op::F64Ne
        | Op::F64Lt
        | Op::F64Gt
        | Op::F64Le
        | Op::F64Ge
        | Op::I32Clz
        | Op::I32Ctz
        | Op::I32Popcnt
        | Op::I32Add
        | Op::I32Sub
        | Op::I32Mul
        | Op::I32DivS
        | Op::I32DivU
        | Op::I32RemS
        | Op::I32RemU
        | Op::I32And
        | Op::I32Or
        | Op::I32Xor
        | Op::I32Shl
        | Op::I32ShrS
        | Op::I32ShrU
        | Op::I32Rotl
        | Op::I32Rotr
        | Op::I64Clz
        | Op::I64Ctz
        | Op::I64Popcnt
        | Op::I64Add
        | Op::I64Sub
        | Op::I64Mul
        | Op::I64DivS
        | Op::I64DivU
        | Op::I64RemS
        | Op::I64RemU
        | Op::I64And
        | Op::I64Or
        | Op::I64Xor
        | Op::I64Shl
        | Op::I64ShrS
        | Op::I64ShrU
        | Op::I64Rotl
        | Op::I64Rotr
        | Op::F32Abs
        | Op::F32Neg
        | Op::F32Ceil
        | Op::F32Floor
        | Op::F32Trunc
        | Op::F32Nearest
        | Op::F32Sqrt
        | Op::F32Add
        | Op::F32Sub
        | Op::F32Mul
        | Op::F32Div
        | Op::F32Min
        | Op::F32Max
        | Op::F32Copysign
        | Op::F64Abs
        | Op::F64Neg
        | Op::F64Ceil
        | Op::F64Floor
        | Op::F64Trunc
        | Op::F64Nearest
        | Op::F64Sqrt
        | Op::F64Add
        | Op::F64Sub
        | Op::F64Mul
        | Op::F64Div
        | Op::F64Min
        | Op::F64Max
        | Op::F64Copysign
        | Op::I32WrapI64
        | Op::I32TruncF32S
        | Op::I32TruncF32U
        | Op::I32TruncF64S
        | Op::I32TruncF64U
        | Op::I64ExtendI32S
        | Op::I64ExtendI32U
        | Op::I64TruncF32S
        | Op::I64TruncF32U
        | Op::I64TruncF64S
        | Op::I64TruncF64U
        | Op::F32ConvertI32S
        | Op::F32ConvertI32U
        | Op::F32ConvertI64S
        | Op::F32ConvertI64U
        | Op::F32DemoteF64
        | Op::F64ConvertI32S
        | Op::F64ConvertI32U
        | Op::F64ConvertI64S
        | Op::F64ConvertI64U
        | Op::F64PromoteF32
        | Op::I32ReinterpretF32
        | Op::I64ReinterpretF64
        | Op::F32ReinterpretI32
        | Op::F64ReinterpretI64
        | Op::I32Extend8S
        | Op::I32Extend16S
        | Op::I64Extend8S
        | Op::I64Extend16S
        | Op::I64Extend32S
        // Ref operations are pure.
        | Op::RefNull { .. }
        | Op::RefIsNull
        | Op::RefFunc { .. }
        // Select is pure.
        | Op::Select { .. }
        // Global get is pure.
        | Op::GlobalGet { .. }
        // Memory and table reads have no side-effects, although I am not sure they are strictly "pure".
        | Op::TableGet { .. }
        | Op::TableSize { .. }
        | Op::I32Load { .. }
        | Op::I64Load { .. }
        | Op::F32Load { .. }
        | Op::F64Load { .. }
        | Op::I32Load8S { .. }
        | Op::I32Load8U { .. }
        | Op::I32Load16S { .. }
        | Op::I32Load16U { .. }
        | Op::I64Load8S { .. }
        | Op::I64Load8U { .. }
        | Op::I64Load16S { .. }
        | Op::I64Load16U { .. }
        | Op::I64Load32S { .. }
        | Op::I64Load32U { .. }
        | Op::V128Load { .. }
        | Op::MemorySize { .. }
        // TODO: there are more WebAssembly 2.0 operations that are missing here...
    ) = &node.operation {
        false
    } else {
        // For now, we consider all non-WASM operations as having side effects.
        true
    }
}
