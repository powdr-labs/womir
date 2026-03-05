//! This pass takes a DAG and removes unnecessary inputs and outputs from
//! blocks. These spurious inputs and outputs may come from the original Wasm
//! code, but they can also be introduced by the `locals_data_flow` pass, which is
//! conservative in its analysis of local usage, or can be orphans from const
//! dedup/collapse.

use crate::loader::passes::calc_input_redirection::RedirDag;

mod bottom_up;
mod top_down;

#[derive(Default, Debug)]
pub struct Statistics {
    pub removed_nodes: usize,
    pub removed_block_outputs: usize,
    pub removed_loop_inputs: usize,
    // We don't track removed block inputs because they have no visible effect
    // on the generated code. They may, however, help remove more nodes and block
    // inputs, which is already counted.
}

/// Prunes block inputs and outputs that are not actually used.
///
/// Returns the statistics of the pruning process.
pub fn prune_block_io(dag: &mut RedirDag<'_>) -> Statistics {
    let mut stats = Statistics::default();

    // If outputs are removed, we might have created new opportunities for
    // input removals, and vice-versa, so we need to repeat until we reach
    // a fixed point.
    let mut must_run_bottom_up = true;
    let mut must_run_top_down = true;
    loop {
        // The sub-pass that removes unused block outputs and pure nodes with no users.
        if must_run_bottom_up {
            let result = bottom_up::remove_useless_outputs(dag);
            stats.removed_nodes += result.removed_nodes;
            stats.removed_block_outputs += result.removed_block_outputs;

            // Either removal of outputs or nodes might leave loop inputs unused,
            // which can be removed by the next top-down sub-pass.
            must_run_top_down |= result.removed_nodes > 0 || result.removed_block_outputs > 0;
            must_run_bottom_up = false;
        }

        if !must_run_bottom_up && !must_run_top_down {
            break;
        }

        // The sub-pass that removes unecessary block inputs. It is more complex because
        // it handles loops, and it alone needs to iterate to reach a fixed point.
        // But we are already in a fixed-point loop, so we just run it once.
        if must_run_top_down {
            let result = top_down::remove_useless_inputs(dag);
            stats.removed_loop_inputs += result.removed_loop_inputs;
            stats.removed_block_outputs += result.removed_block_outputs;

            // If any loop input was removed, we might have left nodes or blocks dangling,
            // that can be removed by the bottom-up sub-pass.
            must_run_bottom_up = result.removed_loop_inputs > 0;

            // If any block output was removed, we might have uncovered new unused loop inputs,
            // that can be removed by the next iteration of the top-down sub-pass.
            must_run_top_down = result.removed_block_outputs > 0;

            // We probably don't have to concern with plain block inputs removed, because
            // any case that doesn't involve a loop input removal would also be covered
            // by the bottom-up sub-pass.
        }

        if !must_run_bottom_up && !must_run_top_down {
            break;
        }
    }

    stats
}

#[cfg(test)]
mod tests {
    use super::prune_block_io;
    use crate::loader::{
        BlockKind,
        passes::{
            calc_input_redirection::{RedirDag, RedirNode, Redirection},
            dag::{BrTableTarget, GenericDag, GenericNode, NodeInput, Operation, ValueOrigin},
        },
    };
    use wasmparser::{Operator as Op, ValType};

    fn input_ref(node: usize, output_idx: u32) -> NodeInput {
        NodeInput::Reference(ValueOrigin::new(node, output_idx))
    }

    /// Assert that `input` is a `Reference` pointing to `(node, output_idx)`.
    fn assert_ref(input: &NodeInput, node: usize, output_idx: u32) {
        match input {
            NodeInput::Reference(origin) => {
                assert_eq!(origin.node, node, "wrong node index");
                assert_eq!(origin.output_idx, output_idx, "wrong output_idx");
            }
            other => panic!("expected Reference({node}, {output_idx}), got {other:?}"),
        }
    }

    fn inputs_node(types: Vec<ValType>) -> RedirNode<'static> {
        GenericNode {
            operation: Operation::Inputs,
            inputs: vec![],
            output_types: types,
        }
    }

    fn br_node(depth: u32, inputs: Vec<NodeInput>) -> RedirNode<'static> {
        GenericNode {
            operation: Operation::WASMOp(Op::Br {
                relative_depth: depth,
            }),
            inputs,
            output_types: vec![],
        }
    }

    fn wasm_op_node(
        op: Op<'static>,
        inputs: Vec<NodeInput>,
        output_types: Vec<ValType>,
    ) -> RedirNode<'static> {
        GenericNode {
            operation: Operation::WASMOp(op),
            inputs,
            output_types,
        }
    }

    fn block_node<'a>(
        inputs: Vec<NodeInput>,
        output_types: Vec<ValType>,
        sub_dag: RedirDag<'a>,
    ) -> RedirNode<'a> {
        GenericNode {
            operation: Operation::Block {
                kind: BlockKind::Block,
                sub_dag,
            },
            inputs,
            output_types,
        }
    }

    fn loop_node<'a>(
        inputs: Vec<NodeInput>,
        output_types: Vec<ValType>,
        sub_dag: RedirDag<'a>,
    ) -> RedirNode<'a> {
        GenericNode {
            operation: Operation::Block {
                kind: BlockKind::Loop,
                sub_dag,
            },
            inputs,
            output_types,
        }
    }

    fn redir_dag(
        nodes: Vec<RedirNode<'static>>,
        block_data: Vec<Redirection>,
    ) -> RedirDag<'static> {
        GenericDag { nodes, block_data }
    }

    fn br_table_node<'a>(
        break_inputs: Vec<NodeInput>,
        selector: NodeInput,
        targets: Vec<BrTableTarget>,
    ) -> RedirNode<'a> {
        let mut inputs = break_inputs;
        inputs.push(selector);
        GenericNode {
            operation: Operation::BrTable { targets },
            inputs,
            output_types: vec![],
        }
    }

    /// An input that is never referenced inside a plain block is removed.
    #[test]
    fn test_unused_block_input_removed() {
        // Function: takes i32, returns nothing.
        // Block: receives the i32 but never uses it; exits immediately.
        let sub_dag = redir_dag(
            vec![inputs_node(vec![ValType::I32]), br_node(0, vec![])],
            vec![],
        );
        let mut dag = redir_dag(
            vec![
                inputs_node(vec![ValType::I32]),
                block_node(vec![input_ref(0, 0)], vec![], sub_dag),
                br_node(0, vec![]),
            ],
            vec![],
        );

        let stats = prune_block_io(&mut dag);

        assert_eq!(stats.removed_loop_inputs, 0);
        assert!(
            dag.nodes[1].inputs.is_empty(),
            "block input should be removed"
        );
        let Operation::Block { ref sub_dag, .. } = dag.nodes[1].operation else {
            panic!()
        };
        assert!(
            sub_dag.nodes[0].output_types.is_empty(),
            "Inputs node should have no outputs"
        );
        assert!(
            sub_dag.block_data.is_empty(),
            "block_data should remain empty"
        );
    }

    /// A plain-block output that is always equal to an input (FromInput) is
    /// removed, its consumers are redirected to the original source, and the
    /// input that only fed that output is also removed.
    #[test]
    fn test_forwarded_output_removed() {
        // Function: takes i32, returns i32 (via block pass-through).
        // Block output 0 = FromInput(0): always equals block input 0.
        let sub_dag = redir_dag(
            vec![
                inputs_node(vec![ValType::I32]),
                br_node(0, vec![input_ref(0, 0)]), // pass input through
            ],
            vec![Redirection::FromInput(0)],
        );
        let mut dag = redir_dag(
            vec![
                inputs_node(vec![ValType::I32]),
                block_node(vec![input_ref(0, 0)], vec![ValType::I32], sub_dag),
                br_node(0, vec![input_ref(1, 0)]), // function return: consumes block output 0
            ],
            vec![Redirection::NotRedirected],
        );

        prune_block_io(&mut dag);

        assert!(
            dag.nodes[1].inputs.is_empty(),
            "block input should be removed"
        );
        assert!(
            dag.nodes[1].output_types.is_empty(),
            "block output should be removed"
        );
        let Operation::Block { ref sub_dag, .. } = dag.nodes[1].operation else {
            panic!()
        };
        assert!(sub_dag.nodes[0].output_types.is_empty());
        assert!(
            sub_dag.nodes[1].inputs.is_empty(),
            "br inside block should have no inputs"
        );
        assert!(
            sub_dag.block_data.is_empty(),
            "block_data should be trimmed to empty"
        );
        // Consumer (function return) should now reference the function input directly.
        assert_ref(&dag.nodes[2].inputs[0], 0, 0);
    }

    /// In a block with two outputs — one computed, one forwarded from an input —
    /// only the forwarded output and its corresponding input are removed.
    /// The computed output and its input are kept. Consumers of the removed
    /// output are redirected to the original source.
    #[test]
    fn test_mixed_block_partial_removal() {
        // Function: takes i32 X (index 0) and i32 Y (index 1), returns two i32s.
        // Block inputs: X, Y.
        // Block outputs:
        //   slot 0: i32.eqz(X)  — computed, NotRedirected
        //   slot 1: Y           — FromInput(1), will be removed
        let sub_dag = redir_dag(
            vec![
                inputs_node(vec![ValType::I32, ValType::I32]),
                wasm_op_node(Op::I32Eqz, vec![input_ref(0, 0)], vec![ValType::I32]), // uses X only
                br_node(0, vec![input_ref(1, 0), input_ref(0, 1)]), // output 0 = eqz(X), output 1 = Y
            ],
            vec![Redirection::NotRedirected, Redirection::FromInput(1)],
        );
        let mut dag = redir_dag(
            vec![
                inputs_node(vec![ValType::I32, ValType::I32]),
                block_node(
                    vec![input_ref(0, 0), input_ref(0, 1)],
                    vec![ValType::I32, ValType::I32],
                    sub_dag,
                ),
                br_node(0, vec![input_ref(1, 0), input_ref(1, 1)]), // function return: both block outputs
            ],
            vec![Redirection::NotRedirected, Redirection::NotRedirected],
        );

        prune_block_io(&mut dag);

        assert_eq!(
            dag.nodes[1].inputs.len(),
            1,
            "only X should remain as block input"
        );
        assert_ref(&dag.nodes[1].inputs[0], 0, 0); // X is still function input 0
        assert_eq!(
            dag.nodes[1].output_types.len(),
            1,
            "only computed output should remain"
        );
        let Operation::Block { ref sub_dag, .. } = dag.nodes[1].operation else {
            panic!()
        };
        // One NotRedirected entry should remain in block_data (slot 0 = eqz(X)).
        assert_eq!(sub_dag.block_data.len(), 1);
        assert_eq!(sub_dag.block_data[0], Redirection::NotRedirected);
        // Consumer of output 0 (computed): still references block output 0.
        assert_ref(&dag.nodes[2].inputs[0], 1, 0);
        // Consumer of output 1 (forwarded Y): redirected to function input 1.
        assert_ref(&dag.nodes[2].inputs[1], 0, 1);
    }

    /// Loop inputs that only pass values around in a cycle — never used by any
    /// computation and never escaping to the outer scope — are all removed.
    #[test]
    fn test_loop_dead_cycle_all_removed() {
        // Loop inputs: A (index 0), B (index 1).
        // Back-edge swaps them: slot 0 ← B, slot 1 ← A.
        // Neither is used in any computation. Both are removable.
        let sub_dag = redir_dag(
            vec![
                inputs_node(vec![ValType::I32, ValType::I32]),
                br_node(0, vec![input_ref(0, 1), input_ref(0, 0)]), // slot 0 ← B (input 1), slot 1 ← A (input 0)
            ],
            vec![Redirection::FromInput(1), Redirection::FromInput(0)],
        );
        let mut dag = redir_dag(
            vec![
                inputs_node(vec![ValType::I32, ValType::I32]),
                loop_node(vec![input_ref(0, 0), input_ref(0, 1)], vec![], sub_dag),
            ],
            vec![],
        );

        let stats = prune_block_io(&mut dag);

        assert_eq!(
            stats.removed_loop_inputs, 2,
            "both loop inputs should be removed"
        );
        assert!(
            dag.nodes[1].inputs.is_empty(),
            "loop node should have no remaining inputs"
        );
        let Operation::Block { ref sub_dag, .. } = dag.nodes[1].operation else {
            panic!()
        };
        assert!(
            sub_dag.nodes[0].output_types.is_empty(),
            "Inputs node should have no outputs"
        );
        assert!(
            sub_dag.nodes[1].inputs.is_empty(),
            "back-edge should have no inputs"
        );
        assert!(
            sub_dag.block_data.is_empty(),
            "loop redirections should be empty"
        );
    }

    /// When at least one loop input is genuinely used in a computation, no inputs
    /// in the cycle are removed.
    #[test]
    fn test_loop_cycle_with_used_input_nothing_removed() {
        // Same swapping loop as above, but input A (index 0) is also consumed
        // by global.set (a side-effectful op). BFS seeds No from A, propagates it to B. Nothing removed.
        let sub_dag = redir_dag(
            vec![
                inputs_node(vec![ValType::I32, ValType::I32]),
                wasm_op_node(
                    Op::GlobalSet { global_index: 0 },
                    vec![input_ref(0, 0)],
                    vec![],
                ), // uses A (side-effectful)
                br_node(0, vec![input_ref(0, 1), input_ref(0, 0)]), // back-edge: slot 0 ← B, slot 1 ← A
            ],
            vec![Redirection::FromInput(1), Redirection::FromInput(0)],
        );
        let mut dag = redir_dag(
            vec![
                inputs_node(vec![ValType::I32, ValType::I32]),
                loop_node(vec![input_ref(0, 0), input_ref(0, 1)], vec![], sub_dag),
            ],
            vec![],
        );

        let stats = prune_block_io(&mut dag);

        assert_eq!(
            stats.removed_loop_inputs, 0,
            "no loop inputs should be removed"
        );
        assert_eq!(
            dag.nodes[1].inputs.len(),
            2,
            "loop should still have 2 inputs"
        );
        assert_ref(&dag.nodes[1].inputs[0], 0, 0); // A
        assert_ref(&dag.nodes[1].inputs[1], 0, 1); // B
        let Operation::Block { ref sub_dag, .. } = dag.nodes[1].operation else {
            panic!()
        };
        assert_eq!(
            sub_dag.nodes[0].output_types.len(),
            2,
            "both Inputs outputs should remain"
        );
        assert_eq!(
            sub_dag.block_data.len(),
            2,
            "loop block_data should be unchanged"
        );
    }

    /// When an inner block's only input is passed straight through as its output
    /// (FromInput), the inner block's I/O is removed. This makes the outer block's
    /// corresponding input entirely unused, so it is also removed.
    #[test]
    fn test_nested_block_input_propagated_removal() {
        // Outer block: inputs A (index 0) and B (index 1).
        //   - A is used by i32.eqz inside the outer block → kept.
        //   - B is only passed to the inner block as its sole input → removable once
        //     the inner block is cleaned.
        // Inner block: sole input = B, sole output = FromInput(0) = B.
        //   The inner block output is not consumed by anything else,
        //   so it is removed along with its input.
        let inner_sub_dag = redir_dag(
            vec![
                inputs_node(vec![ValType::I32]),   // Node 0: B
                br_node(0, vec![input_ref(0, 0)]), // Node 1: pass B as output slot 0
            ],
            vec![Redirection::FromInput(0)], // output 0 = always its input B
        );
        let outer_sub_dag = redir_dag(
            vec![
                inputs_node(vec![ValType::I32, ValType::I32]), // Node 0: A, B
                wasm_op_node(Op::I32Eqz, vec![input_ref(0, 0)], vec![ValType::I32]), // Node 1: eqz(A)
                block_node(
                    // Node 2: inner block
                    vec![input_ref(0, 1)], // input: B
                    vec![ValType::I32],    // output: one i32 (will be removed)
                    inner_sub_dag,
                ),
                br_node(0, vec![input_ref(1, 0)]), // Node 3: break with eqz(A) as outer block's output
            ],
            vec![Redirection::NotRedirected], // outer block's one output is computed, not redirected
        );
        let mut dag = redir_dag(
            vec![
                inputs_node(vec![ValType::I32, ValType::I32]), // Node 0: function inputs A, B
                block_node(
                    vec![input_ref(0, 0), input_ref(0, 1)], // pass A and B into outer block
                    vec![ValType::I32],                     // outer block produces one i32
                    outer_sub_dag,
                ),
                br_node(0, vec![input_ref(1, 0)]), // Node 2: function return = outer block output 0
            ],
            vec![Redirection::NotRedirected],
        );

        let stats = prune_block_io(&mut dag);

        assert_eq!(stats.removed_loop_inputs, 0);

        // Outer block: B (index 1) should be removed, only A remains.
        assert_eq!(
            dag.nodes[1].inputs.len(),
            1,
            "only A should remain as outer block input"
        );
        assert_ref(&dag.nodes[1].inputs[0], 0, 0); // still A
        assert_eq!(
            dag.nodes[1].output_types.len(),
            1,
            "outer block output unchanged"
        );

        let Operation::Block { ref sub_dag, .. } = dag.nodes[1].operation else {
            panic!()
        };

        // Outer sub_dag Inputs: only A's slot should remain.
        assert_eq!(
            sub_dag.nodes[0].output_types.len(),
            1,
            "only A in Inputs node"
        );

        // Inner block node (sub_dag.nodes[2]): no inputs, no outputs.
        assert!(
            sub_dag.nodes[2].inputs.is_empty(),
            "inner block inputs cleared"
        );
        assert!(
            sub_dag.nodes[2].output_types.is_empty(),
            "inner block outputs cleared"
        );

        // Inner block's own sub_dag should be fully empty.
        let Operation::Block {
            sub_dag: ref inner_sub_dag,
            ..
        } = sub_dag.nodes[2].operation
        else {
            panic!()
        };
        assert!(
            inner_sub_dag.nodes[0].output_types.is_empty(),
            "inner Inputs node is empty"
        );
        assert!(
            inner_sub_dag.nodes[1].inputs.is_empty(),
            "inner Br has no inputs"
        );

        // Function return is unchanged.
        assert_ref(&dag.nodes[2].inputs[0], 1, 0);
    }

    /// Two sequential plain blocks, B1 and B2, each forwarding their sole input as
    /// their sole output (FromInput). B2's input is B1's output. Both are fully
    /// cleaned and the function return ends up pointing straight at the original
    /// function input.
    #[test]
    fn test_chained_output_substitution() {
        // B1: input=A (function input 0), output=FromInput(0)=A.
        let b1_sub_dag = redir_dag(
            vec![
                inputs_node(vec![ValType::I32]),   // Node 0: A
                br_node(0, vec![input_ref(0, 0)]), // Node 1: pass A to output slot 0
            ],
            vec![Redirection::FromInput(0)],
        );
        // B2: input=B1's output 0, output=FromInput(0)=its input.
        let b2_sub_dag = redir_dag(
            vec![
                inputs_node(vec![ValType::I32]),   // Node 0: B2's input
                br_node(0, vec![input_ref(0, 0)]), // Node 1: pass input to output slot 0
            ],
            vec![Redirection::FromInput(0)],
        );
        let mut dag = redir_dag(
            vec![
                inputs_node(vec![ValType::I32]), // Node 0: function input A
                block_node(vec![input_ref(0, 0)], vec![ValType::I32], b1_sub_dag), // Node 1: B1
                block_node(vec![input_ref(1, 0)], vec![ValType::I32], b2_sub_dag), // Node 2: B2
                br_node(0, vec![input_ref(2, 0)]), // Node 3: function return = B2 output 0
            ],
            vec![Redirection::NotRedirected],
        );

        let stats = prune_block_io(&mut dag);

        assert_eq!(stats.removed_loop_inputs, 0);

        // Both blocks should be fully cleaned.
        assert!(dag.nodes[1].inputs.is_empty(), "B1 should have no inputs");
        assert!(
            dag.nodes[1].output_types.is_empty(),
            "B1 should have no outputs"
        );
        assert!(dag.nodes[2].inputs.is_empty(), "B2 should have no inputs");
        assert!(
            dag.nodes[2].output_types.is_empty(),
            "B2 should have no outputs"
        );

        // Inner sub-dags should be fully cleaned too.
        let Operation::Block {
            sub_dag: ref b1_sub,
            ..
        } = dag.nodes[1].operation
        else {
            panic!()
        };
        assert!(b1_sub.nodes[0].output_types.is_empty());
        assert!(b1_sub.nodes[1].inputs.is_empty());
        assert!(b1_sub.block_data.is_empty());
        let Operation::Block {
            sub_dag: ref b2_sub,
            ..
        } = dag.nodes[2].operation
        else {
            panic!()
        };
        assert!(b2_sub.nodes[0].output_types.is_empty());
        assert!(b2_sub.nodes[1].inputs.is_empty());
        assert!(b2_sub.block_data.is_empty());

        // Function return should now reference the original function input directly.
        assert_eq!(dag.nodes[3].inputs.len(), 1);
        assert_ref(&dag.nodes[3].inputs[0], 0, 0);
    }

    /// A BrTable inside a plain block has two targets with permutations [0,1,2] and
    /// [2,1,0]. The block's middle output slot (index 1) is always equal to block
    /// input B (FromInput(1)), so it is shortcircuited. The corresponding permutation
    /// entry (index 1) is removed from every target, and B — no longer referenced by
    /// any target — is pruned from the BrTable's node inputs. Permutation indices are
    /// renumbered after the removal.
    #[test]
    fn test_br_table_partial_target_overlap() {
        // Block: inputs A (0), B (1), C (2); outputs: [NotRedirected, FromInput(1), NotRedirected].
        // BrTable break_inputs = [A, B, C]; selector = A (making A "Used").
        // Target 0: perm [0,1,2] → slot0=A, slot1=B, slot2=C.
        // Target 1: perm [2,1,0] → slot0=C, slot1=B, slot2=A.
        // Both send B to slot 1, confirming FromInput(1).
        let sub_dag = redir_dag(
            vec![
                inputs_node(vec![ValType::I32, ValType::I32, ValType::I32]), // Node 0: A, B, C
                br_table_node(
                    vec![input_ref(0, 0), input_ref(0, 1), input_ref(0, 2)], // break inputs: A, B, C
                    input_ref(0, 0), // selector = A (marks A as Used)
                    vec![
                        BrTableTarget {
                            relative_depth: 0,
                            input_permutation: vec![0, 1, 2],
                        },
                        BrTableTarget {
                            relative_depth: 0,
                            input_permutation: vec![2, 1, 0],
                        },
                    ],
                ),
            ],
            vec![
                Redirection::NotRedirected,
                Redirection::FromInput(1),
                Redirection::NotRedirected,
            ],
        );
        let mut dag = redir_dag(
            vec![
                inputs_node(vec![ValType::I32, ValType::I32, ValType::I32]), // Node 0: A, B, C
                block_node(
                    vec![input_ref(0, 0), input_ref(0, 1), input_ref(0, 2)],
                    vec![ValType::I32, ValType::I32, ValType::I32],
                    sub_dag,
                ),
                br_node(0, vec![input_ref(1, 0), input_ref(1, 1), input_ref(1, 2)]), // function return: all 3 block outputs
            ],
            vec![
                Redirection::NotRedirected,
                Redirection::NotRedirected,
                Redirection::NotRedirected,
            ],
        );

        prune_block_io(&mut dag);

        // Block input B (index 1) should be removed; A and C remain.
        assert_eq!(
            dag.nodes[1].inputs.len(),
            2,
            "A and C remain as block inputs"
        );
        assert_ref(&dag.nodes[1].inputs[0], 0, 0); // A
        assert_ref(&dag.nodes[1].inputs[1], 0, 2); // C

        // Block output slot 1 should be removed; 2 outputs remain.
        assert_eq!(dag.nodes[1].output_types.len(), 2);

        // Consumer of old output 1 (B) is redirected to function input B.
        // Consumer of old output 2 (C-or-A) has its index shifted from 2 to 1.
        assert_ref(&dag.nodes[2].inputs[0], 1, 0); // block output 0 unchanged
        assert_ref(&dag.nodes[2].inputs[1], 0, 1); // redirected to function input B
        assert_ref(&dag.nodes[2].inputs[2], 1, 1); // block output 2 shifted to slot 1

        let Operation::Block { ref sub_dag, .. } = dag.nodes[1].operation else {
            panic!()
        };

        // Inputs node inside block: B's slot removed, 2 remain.
        assert_eq!(sub_dag.nodes[0].output_types.len(), 2);

        // BrTable node: break_inputs become [A, C_shifted]; selector unchanged.
        assert_eq!(
            sub_dag.nodes[1].inputs.len(),
            3,
            "two break inputs + selector"
        );
        assert_ref(&sub_dag.nodes[1].inputs[0], 0, 0); // A (break input 0)
        assert_ref(&sub_dag.nodes[1].inputs[1], 0, 1); // C (shifted from r(0,2) → r(0,1))
        assert_ref(&sub_dag.nodes[1].inputs[2], 0, 0); // selector = A

        // Permutations after removal of slot 1 and re-indexing.
        let Operation::BrTable { ref targets } = sub_dag.nodes[1].operation else {
            panic!()
        };
        assert_eq!(targets[0].input_permutation, vec![0u32, 1u32]); // was [0,2], C now at index 1
        assert_eq!(targets[1].input_permutation, vec![1u32, 0u32]); // was [2,0], C now at index 1
    }

    /// When a BrIf's break input is removed, its selector (condition) is preserved.
    #[test]
    fn test_br_if_selector_preserved_when_break_input_pruned() {
        // Block: inputs A (0) and B (1); one output = A = FromInput(0).
        // BrIf: break input = A (slot 0), selector = B (last input).
        //   → A is removable (only forwarded to the shortcircuited output).
        //   → B is Used (it is the selector, treated as a normal node input).
        let sub_dag = redir_dag(
            vec![
                inputs_node(vec![ValType::I32, ValType::I32]), // Node 0: A, B
                GenericNode {
                    operation: Operation::WASMOp(Op::BrIf { relative_depth: 0 }),
                    inputs: vec![input_ref(0, 0), input_ref(0, 1)], // [break=A, selector=B]
                    output_types: vec![],
                },
            ],
            vec![Redirection::FromInput(0)], // output 0 = A
        );
        let mut dag = redir_dag(
            vec![
                inputs_node(vec![ValType::I32, ValType::I32]), // Node 0: A, B
                block_node(
                    vec![input_ref(0, 0), input_ref(0, 1)],
                    vec![ValType::I32],
                    sub_dag,
                ),
                br_node(0, vec![input_ref(1, 0)]), // function return = block output 0
            ],
            vec![Redirection::NotRedirected],
        );

        prune_block_io(&mut dag);

        // Block: A removed, only B remains as input; output removed.
        assert_eq!(dag.nodes[1].inputs.len(), 1, "only B should remain");
        assert_ref(&dag.nodes[1].inputs[0], 0, 1); // B
        assert!(dag.nodes[1].output_types.is_empty(), "output removed");

        let Operation::Block { ref sub_dag, .. } = dag.nodes[1].operation else {
            panic!()
        };
        assert!(sub_dag.block_data.is_empty());

        // BrIf: break input A removed; selector B survives as the sole input.
        // After B shifts from index 1 to index 0 in the Inputs node, B is r(0,0).
        assert_eq!(
            sub_dag.nodes[1].inputs.len(),
            1,
            "only the selector should remain"
        );
        assert_ref(&sub_dag.nodes[1].inputs[0], 0, 0); // B (shifted from r(0,1) to r(0,0))

        // Consumer of the removed output is redirected to function input A.
        assert_ref(&dag.nodes[2].inputs[0], 0, 0); // A
    }

    /// When an inner block breaks to an outer block (depth > 0) and the outer block's
    /// output is shortcircuited, the corresponding break input inside the inner block
    /// is correctly removed.
    #[test]
    fn test_nested_relative_depth_break_removal() {
        // Outer block: one input A, one output = A = FromInput(0).
        // Inside outer block: an inner block whose only content is a Br at depth=1
        // (targeting the outer block) that passes A as the single output value.
        // After pruning: output shortcircuited, A removed, Br at depth=1 emptied.
        let inner_sub_dag = redir_dag(
            vec![
                inputs_node(vec![ValType::I32]),   // Node 0: A (inner block's input)
                br_node(1, vec![input_ref(0, 0)]), // Node 1: Br depth=1, passes A to outer output slot 0
            ],
            vec![], // inner block has no outputs of its own
        );
        let outer_sub_dag = redir_dag(
            vec![
                inputs_node(vec![ValType::I32]), // Node 0: A
                block_node(
                    // Node 1: inner block
                    vec![input_ref(0, 0)], // passes A in
                    vec![],
                    inner_sub_dag,
                ),
            ],
            vec![Redirection::FromInput(0)], // outer block's output 0 = always A
        );
        let mut dag = redir_dag(
            vec![
                inputs_node(vec![ValType::I32]), // Node 0: function input A
                block_node(vec![input_ref(0, 0)], vec![ValType::I32], outer_sub_dag),
                br_node(0, vec![input_ref(1, 0)]), // Node 2: function return = outer block output 0
            ],
            vec![Redirection::NotRedirected],
        );

        prune_block_io(&mut dag);

        // Outer block fully cleaned.
        assert!(dag.nodes[1].inputs.is_empty());
        assert!(dag.nodes[1].output_types.is_empty());

        let Operation::Block { ref sub_dag, .. } = dag.nodes[1].operation else {
            panic!()
        };
        assert!(sub_dag.nodes[0].output_types.is_empty()); // Inputs node: A removed
        assert!(sub_dag.nodes[1].inputs.is_empty()); // inner block: no inputs
        assert!(sub_dag.nodes[1].output_types.is_empty()); // inner block: no outputs

        // Inner block's Br at depth=1 should have had its input removed.
        let Operation::Block {
            sub_dag: ref inner_sub,
            ..
        } = sub_dag.nodes[1].operation
        else {
            panic!()
        };
        assert!(inner_sub.nodes[0].output_types.is_empty()); // inner Inputs node: A removed
        assert!(
            inner_sub.nodes[1].inputs.is_empty(),
            "Br at depth=1 should have no inputs"
        );

        // Function return redirected to A directly.
        assert_ref(&dag.nodes[2].inputs[0], 0, 0);
    }

    /// In a loop where some inputs form a dead cycle and others are genuinely used,
    /// only the dead-cycle inputs are removed.
    #[test]
    fn test_loop_partial_cycle_prunes_only_disconnected_component() {
        // Loop inputs: A (0), B (1), C (2).
        // Back-edge: slot 0 ← B (FromInput(1)), slot 1 ← A (FromInput(0)),
        //            slot 2 ← C (FromInput(2)).
        // A and B swap each other each iteration and are never used → removable.
        // C is consumed by global.set (side-effectful) → Not removable; BFS from C does not reach A or B.
        let sub_dag = redir_dag(
            vec![
                inputs_node(vec![ValType::I32, ValType::I32, ValType::I32]),
                wasm_op_node(
                    Op::GlobalSet { global_index: 0 },
                    vec![input_ref(0, 2)],
                    vec![],
                ), // uses C (side-effectful)
                // back-edge: [B, A, C] — slot 0←B, slot 1←A, slot 2←C
                br_node(0, vec![input_ref(0, 1), input_ref(0, 0), input_ref(0, 2)]),
            ],
            vec![
                Redirection::FromInput(1), // slot 0 ← B
                Redirection::FromInput(0), // slot 1 ← A
                Redirection::FromInput(2), // slot 2 ← C
            ],
        );
        let mut dag = redir_dag(
            vec![
                inputs_node(vec![ValType::I32, ValType::I32, ValType::I32]),
                loop_node(
                    vec![input_ref(0, 0), input_ref(0, 1), input_ref(0, 2)],
                    vec![],
                    sub_dag,
                ),
            ],
            vec![],
        );

        let stats = prune_block_io(&mut dag);

        assert_eq!(stats.removed_loop_inputs, 2, "A and B should be removed");

        // Loop node: only C remains as input.
        assert_eq!(dag.nodes[1].inputs.len(), 1);
        assert_ref(&dag.nodes[1].inputs[0], 0, 2); // C (still references function input 2)

        let Operation::Block { ref sub_dag, .. } = dag.nodes[1].operation else {
            panic!()
        };

        // Inputs node: only C's slot remains.
        assert_eq!(sub_dag.nodes[0].output_types.len(), 1);

        // WASMOp: still references C, now shifted to index 0.
        assert_eq!(sub_dag.nodes[1].inputs.len(), 1);
        assert_ref(&sub_dag.nodes[1].inputs[0], 0, 0); // C shifted to r(0,0)

        // Back-edge: only C remains, shifted to r(0,0).
        assert_eq!(sub_dag.nodes[2].inputs.len(), 1);
        assert_ref(&sub_dag.nodes[2].inputs[0], 0, 0); // C shifted

        // block_data: only C's entry remains, re-indexed to FromInput(0).
        assert_eq!(sub_dag.block_data.len(), 1);
        assert_eq!(sub_dag.block_data[0], Redirection::FromInput(0));
    }
}
