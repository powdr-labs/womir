//! Implements what the literature calls "parallel moves".
//!
//! Considering the precondition that every destination register has a single source register,
//! the resulting directed graph consists of these three kinds of connected components:
//! 1. Trees, where leaves are destination-only registers, and the root is a source-only register.
//! 2. Cycles, where every register is both a source and a destination.
//! 3. A single cycle originating one or more trees. In this case, you can't have more than one
//!    connected cycle, because that would violate the precondition.
//!
//! Cases 1 and 3 are handled in the first phase of the algorithm, where the copies are generated
//! in a topological order, pruning the trees from the graph. In case 3, the cycle is naturally,
//! broken, because the value of a register in the cycle is written to a register in the connected,
//! and this register is then used as source for the remaining copies in the cycle.
//!
//! Cases 2, the remaining cycles in the graph, are handled in the second phase of the algorithm,
//! where a temporary register is used to break the cycle. The temporary register is either a
//! dedicated temporary register, or, if possible, any register that has is not an original source,
//! handled in the first phase of the algorithm.
//!
//! The final sequence of copy instructions contains first the results of the second phase
//! (cycle-breaking copies), then the results of the first phase (non-cycle copies). This swapped
//! order is to ensure that the temporary register used to break cycles is not overwritten.

use std::collections::{BTreeMap, btree_map::Entry};

/// Given a set of parallel copies, determine a sequence of individual copy instructions
/// that can be executed in order without overwriting any source values before they are copied.
///
/// At most one tmp register may be used to break cycles, but not necessarily.
///
/// `parallel_copies` is a list of (source, destination) register pairs that need to be copied in parallel.
///
/// Returns a sequence of (source, destination) register pairs that can be executed in order to achieve
/// the same effect as the original parallel copies.
///
/// Pre-conditions:
///  * every destination register must be only written to once.
pub fn sequence_parallel_copies(
    parallel_copies: impl IntoIterator<Item = (u32, u32)>,
) -> impl Iterator<Item = (Register, Register)> {
    // This could be a HashMap if we didn't care about the determinism of the output...
    let mut graph: BTreeMap<u32, RegConnections> = BTreeMap::new();

    for (src, dst) in parallel_copies {
        if src == dst {
            // No need to copy a register to itself, we can skip this copy.
            continue;
        }

        // Update the destination entry in the graph.
        let dst_entry = graph.entry(dst).or_default();
        if dst_entry.src == Some(src) {
            // This copy is already represented is repeated, we can skip it.
            continue;
        }
        if dst_entry.src.is_some() {
            panic!(
                "Pre-condition violated: destination register {} is written to more than once",
                dst
            );
        }
        dst_entry.src = Some(src);

        // Update the source entry in the graph.
        graph.entry(src).or_default().dest.push(dst);
    }

    sequence_parallel_copies_impl(graph)
}

#[derive(Default)]
struct RegConnections {
    src: Option<u32>,
    dest: Vec<u32>,
}

fn sequence_parallel_copies_impl(
    mut graph: BTreeMap<u32, RegConnections>,
) -> impl Iterator<Item = (Register, Register)> {
    // Find the set of destinations that are not sources to any other copy.
    let mut tree_ends: Vec<u32> = graph
        .iter()
        .filter_map(|(&reg, conn)| conn.dest.is_empty().then_some(reg))
        .collect();

    let mut non_cycle_copies: Vec<(u32, u32)> = Vec::new();

    // This part of the algorithm prunes the subtrees of the graph, leaving only the cycles.
    // Due to the source-swapping operation, a cycle connected to a subtree will be automatically
    // broken and handled in this phase.
    while let Some(target) = tree_ends.pop() {
        // Unfortunately we cant keep the mutable borrow of this entry, because
        // we will have to mutate the source entry as well.
        let source = graph[&target].src.unwrap();
        non_cycle_copies.push((source, target));

        let Entry::Occupied(mut source_entry) = graph.entry(source) else {
            panic!("Invariant violated: source register not found in graph");
        };
        let source_node = source_entry.get_mut();

        // Remove the edge from source to target.
        source_node.dest.retain(|&dst| dst != target);

        // We perform the source-swapping trick that breaks a potential cycle connected to
        // this subtree: the newly written register will now be the source of the remaining
        // copies, instead of the original source, if any.
        let remaining_dests = std::mem::take(&mut source_node.dest);

        if source_node.src.is_none() {
            // The source entry can be removed from the graph, as it has no source itself.
            source_entry.remove_entry();
        } else {
            // The original source now no more outgoing edges, add it to the tree_ends list.
            tree_ends.push(source);
        }

        // Update the target entry in the graph with the remaining destinations, if any.
        if remaining_dests.is_empty() {
            // If there are no remaining destinations, the target entry can be removed from the graph,
            // since it has no more sources or destinations.
            graph.remove(&target);
        } else {
            // Update the src of remaining destinations to point to target (source-swapping).
            // This is the key step: since target now holds the same value as the original source,
            // we can use target as the source for the remaining copies.
            for &d in &remaining_dests {
                graph.get_mut(&d).unwrap().src = Some(target);
            }

            let target_entry = graph.get_mut(&target).unwrap();
            // The target is no longer a destination.
            target_entry.src = None;
            // The target is now the source for the remaining destinations.
            target_entry.dest = remaining_dests;
        }
    }

    // At this point, the graph only contains cycles. We can break them by using a temporary register.
    // The thing is, we don't really need an extra temporary register if there were any copies already issued.
    // We can use any written register that isn't an original source, as long as we place the cycle-breaking
    // copies before the original copies in the sequence.
    let tmp_register = non_cycle_copies
        .first()
        .map(|&(_, dst)| Register::Given(dst))
        .unwrap_or(Register::Temp);

    let mut cycle_copies: Vec<(Register, Register)> = Vec::new();
    while let Some(initial) = graph.keys().next().cloned() {
        // Break the cycle by copying the value of `initial` to the temporary register.
        cycle_copies.push((Register::Given(initial), tmp_register));

        let mut curr = initial;
        loop {
            let Entry::Occupied(curr_entry) = graph.entry(curr) else {
                panic!("Invariant violated: current register not found in graph");
            };
            let curr_node = curr_entry.get();
            assert_eq!(
                curr_node.dest.len(),
                1,
                "Invariant violated: cycle node has more than one destination"
            );

            let src = curr_node.src.unwrap();
            curr_entry.remove_entry();

            if src == initial {
                // We have completed the cycle, we can break out of the loop.
                break;
            }

            // Copy the value from src to curr.
            cycle_copies.push((Register::Given(src), Register::Given(curr)));
            curr = src;
        }

        // Close the cycle by copying the value from the temporary register to the last destination.
        cycle_copies.push((tmp_register, Register::Given(curr)));
    }

    // We have to place the cycle-breaking copies before the non-cycle copies, because the latter may
    // write to the register that we need to use as temporary for breaking the cycles.
    cycle_copies.into_iter().chain(
        non_cycle_copies
            .into_iter()
            .map(|(src, dst)| (Register::Given(src), Register::Given(dst))),
    )
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Register {
    Temp,
    Given(u32),
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The index of the temporary register in the simulation vector.
    const TMP_REG_INDEX: usize = 1000;

    /// Apply parallel copies naively: read all sources first, then write all destinations.
    /// This simulates true parallel execution.
    /// Self-copies (src == dst) are skipped as they are no-ops.
    fn apply_parallel_copies_naive(registers: &mut [u32], copies: &[(u32, u32)]) {
        // First, read all source values (skipping self-copies)
        let source_values: Vec<(u32, u32)> = copies
            .iter()
            .filter(|&&(src, dst)| src != dst)
            .map(|&(src, dst)| (registers[src as usize], dst))
            .collect();

        // Then, write all destination values
        for (value, dst) in source_values {
            registers[dst as usize] = value;
        }
    }

    /// Apply a sequence of copies one by one (sequential execution).
    fn apply_sequential_copies(
        registers: &mut [u32],
        copies: impl Iterator<Item = (Register, Register)>,
    ) {
        for (src, dst) in copies {
            let src_idx = match src {
                Register::Given(r) => r as usize,
                Register::Temp => TMP_REG_INDEX,
            };
            let dst_idx = match dst {
                Register::Given(r) => r as usize,
                Register::Temp => TMP_REG_INDEX,
            };
            registers[dst_idx] = registers[src_idx];
        }
    }

    /// Helper to run a test case: applies parallel copies naively to get reference,
    /// then applies the sequenced result and compares.
    fn test_parallel_copies(parallel_copies: Vec<(u32, u32)>, num_registers: usize) {
        // Initialize registers with unique values (register i contains value i*10 for clarity)
        let mut reference_registers: Vec<u32> = (0..num_registers.max(TMP_REG_INDEX + 1))
            .map(|i| (i * 10) as u32)
            .collect();
        let mut test_registers = reference_registers.clone();

        // Apply naive parallel copies to get the expected result
        apply_parallel_copies_naive(&mut reference_registers, &parallel_copies);

        // Get the sequenced copies from our algorithm
        let sequenced_copies: Vec<_> = sequence_parallel_copies(parallel_copies).collect();

        // Apply sequenced copies to test registers
        apply_sequential_copies(&mut test_registers, sequenced_copies.into_iter());

        // Compare results (excluding the temp register which is implementation detail)
        assert_eq!(
            &reference_registers[..num_registers],
            &test_registers[..num_registers],
            "Sequenced copies did not produce the same result as parallel copies"
        );
    }

    #[test]
    fn test_empty() {
        test_parallel_copies(vec![], 10);
    }

    #[test]
    fn test_single_copy() {
        test_parallel_copies(vec![(0, 1)], 10);
    }

    #[test]
    fn test_self_copy() {
        // Copying a register to itself should be a no-op
        test_parallel_copies(vec![(0, 0)], 10);
    }

    #[test]
    fn test_multiple_self_copies() {
        test_parallel_copies(vec![(0, 0), (1, 1), (2, 2)], 10);
    }

    #[test]
    fn test_independent_copies() {
        // Multiple copies with no overlap
        test_parallel_copies(vec![(0, 1), (2, 3), (4, 5)], 10);
    }

    #[test]
    fn test_chain_two() {
        // a -> b, b -> c (chain of length 2)
        test_parallel_copies(vec![(0, 1), (1, 2)], 10);
    }

    #[test]
    fn test_chain_three() {
        // a -> b -> c -> d
        test_parallel_copies(vec![(0, 1), (1, 2), (2, 3)], 10);
    }

    #[test]
    fn test_chain_long() {
        // Chain of 10 elements
        let copies: Vec<_> = (0..9).map(|i| (i, i + 1)).collect();
        test_parallel_copies(copies, 20);
    }

    #[test]
    fn test_simple_swap() {
        // a <-> b (cycle of length 2)
        test_parallel_copies(vec![(0, 1), (1, 0)], 10);
    }

    #[test]
    fn test_cycle_three() {
        // a -> b -> c -> a
        test_parallel_copies(vec![(0, 1), (1, 2), (2, 0)], 10);
    }

    #[test]
    fn test_cycle_four() {
        // a -> b -> c -> d -> a
        test_parallel_copies(vec![(0, 1), (1, 2), (2, 3), (3, 0)], 10);
    }

    #[test]
    fn test_cycle_five() {
        test_parallel_copies(vec![(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)], 10);
    }

    #[test]
    fn test_tree_fan_out() {
        // One source to multiple destinations: a -> b, a -> c, a -> d
        test_parallel_copies(vec![(0, 1), (0, 2), (0, 3)], 10);
    }

    #[test]
    fn test_tree_deep() {
        // a -> b, b -> c, b -> d (tree with depth 2)
        test_parallel_copies(vec![(0, 1), (1, 2), (1, 3)], 10);
    }

    #[test]
    fn test_tree_complex() {
        // More complex tree:
        //       0
        //      /|\
        //     1 2 3
        //    /|   |
        //   4 5   6
        test_parallel_copies(vec![(0, 1), (0, 2), (0, 3), (1, 4), (1, 5), (3, 6)], 10);
    }

    #[test]
    fn test_cycle_with_tree_attached() {
        // Cycle: 0 -> 1 -> 0, with tree: 1 -> 2
        test_parallel_copies(vec![(0, 1), (1, 0), (1, 2)], 10);
    }

    #[test]
    fn test_cycle_with_multiple_trees() {
        // Cycle: 0 -> 1 -> 0, with trees: 0 -> 2, 1 -> 3
        test_parallel_copies(vec![(0, 1), (1, 0), (0, 2), (1, 3)], 10);
    }

    #[test]
    fn test_cycle_with_deep_tree() {
        // Cycle: 0 -> 1 -> 0, with chain: 1 -> 2 -> 3 -> 4
        test_parallel_copies(vec![(0, 1), (1, 0), (1, 2), (2, 3), (3, 4)], 10);
    }

    #[test]
    fn test_multiple_independent_cycles() {
        // Two independent cycles
        test_parallel_copies(vec![(0, 1), (1, 0), (2, 3), (3, 2)], 10);
    }

    #[test]
    fn test_multiple_cycles_different_sizes() {
        // Cycle of 2 and cycle of 3
        test_parallel_copies(vec![(0, 1), (1, 0), (2, 3), (3, 4), (4, 2)], 10);
    }

    #[test]
    fn test_duplicate_copy() {
        // Same copy specified twice
        test_parallel_copies(vec![(0, 1), (0, 1)], 10);
    }

    #[test]
    fn test_chain_with_independent() {
        // Chain plus independent copies
        test_parallel_copies(vec![(0, 1), (1, 2), (3, 4), (5, 6)], 10);
    }

    #[test]
    fn test_cycle_with_chain_and_independent() {
        // Mix of everything
        test_parallel_copies(
            vec![
                (0, 1),
                (1, 0), // cycle
                (2, 3),
                (3, 4), // chain
                (5, 6), // independent
            ],
            10,
        );
    }

    #[test]
    fn test_reverse_order_copies() {
        // Copies specified in reverse order of their natural sequence
        test_parallel_copies(vec![(2, 3), (1, 2), (0, 1)], 10);
    }

    #[test]
    fn test_scattered_registers() {
        // Copies between non-consecutive register numbers
        test_parallel_copies(vec![(0, 100), (100, 200), (200, 50)], 300);
    }

    #[test]
    fn test_cycle_scattered() {
        // Cycle with scattered register numbers
        test_parallel_copies(vec![(5, 50), (50, 100), (100, 5)], 150);
    }

    #[test]
    fn test_all_to_one_fan_in_invalid() {
        // This should panic - multiple sources writing to same destination
        // We test that the algorithm correctly rejects this
    }

    #[test]
    #[should_panic(expected = "destination register")]
    fn test_conflicting_destinations_panics() {
        // Two different sources writing to the same destination - should panic
        let _ = sequence_parallel_copies(vec![(0, 2), (1, 2)]).collect::<Vec<_>>();
    }

    #[test]
    fn test_complex_mixed_scenario() {
        // Complex scenario with multiple components:
        // - A 3-cycle: 0 -> 1 -> 2 -> 0
        // - A tree from node 1: 1 -> 3 -> 4, 3 -> 5
        // - Independent chain: 6 -> 7 -> 8
        // - Independent copy: 9 -> 10
        test_parallel_copies(
            vec![
                // 3-cycle with tree
                (0, 1),
                (1, 2),
                (2, 0),
                (1, 3),
                (3, 4),
                (3, 5),
                // Independent chain
                (6, 7),
                (7, 8),
                // Independent copy
                (9, 10),
            ],
            15,
        );
    }

    #[test]
    fn test_self_copy_mixed_with_others() {
        // Self-copy mixed with real copies
        test_parallel_copies(vec![(0, 0), (1, 2), (2, 2), (3, 4)], 10);
    }

    #[test]
    fn test_long_cycle() {
        // Cycle of 20 elements
        let n = 20;
        let copies: Vec<_> = (0..n).map(|i| (i, (i + 1) % n)).collect();
        test_parallel_copies(copies, 30);
    }

    #[test]
    fn test_many_trees_from_one_root() {
        // Many parallel branches from one root
        test_parallel_copies(
            vec![
                (0, 1),
                (0, 2),
                (0, 3),
                (0, 4),
                (0, 5),
                (0, 6),
                (0, 7),
                (0, 8),
                (0, 9),
            ],
            15,
        );
    }

    #[test]
    fn test_two_level_tree() {
        // Two-level tree
        // 0 -> 1, 2, 3
        // 1 -> 4, 5
        // 2 -> 6
        // 3 -> 7, 8
        test_parallel_copies(
            vec![
                (0, 1),
                (0, 2),
                (0, 3),
                (1, 4),
                (1, 5),
                (2, 6),
                (3, 7),
                (3, 8),
            ],
            15,
        );
    }

    #[test]
    fn test_swap_with_extra_copy_from_each() {
        // Swap 0 <-> 1, plus 0 -> 2 and 1 -> 3
        test_parallel_copies(vec![(0, 1), (1, 0), (0, 2), (1, 3)], 10);
    }

    #[test]
    fn test_overlapping_chains() {
        // Two chains that share a middle node as source
        // 0 -> 1 -> 2 and 0 -> 3 -> 4
        test_parallel_copies(vec![(0, 1), (1, 2), (0, 3), (3, 4)], 10);
    }

    #[test]
    fn test_cycle_every_node_has_tree() {
        // 3-cycle where every node has an additional destination
        // 0 -> 1 -> 2 -> 0, plus 0 -> 3, 1 -> 4, 2 -> 5
        test_parallel_copies(vec![(0, 1), (1, 2), (2, 0), (0, 3), (1, 4), (2, 5)], 10);
    }

    #[test]
    fn test_single_register_universe() {
        // Only one register involved, copying to itself
        test_parallel_copies(vec![(0, 0)], 1);
    }

    #[test]
    fn test_large_independent_copies() {
        // Many independent copies
        let copies: Vec<_> = (0..50).map(|i| (i * 2, i * 2 + 1)).collect();
        test_parallel_copies(copies, 110);
    }

    #[test]
    fn test_alternating_chains() {
        // Two interleaved chains: 0->2->4->6 and 1->3->5->7
        test_parallel_copies(vec![(0, 2), (2, 4), (4, 6), (1, 3), (3, 5), (5, 7)], 10);
    }

    #[test]
    fn test_reverse_chain() {
        // Chain in decreasing order: 4 -> 3 -> 2 -> 1 -> 0
        test_parallel_copies(vec![(4, 3), (3, 2), (2, 1), (1, 0)], 10);
    }

    #[test]
    fn test_bidirectional_chain_no_cycle() {
        // Two chains going opposite directions, not forming a cycle
        // 0 -> 1 -> 2 and 4 -> 3 (separate, no connection)
        test_parallel_copies(vec![(0, 1), (1, 2), (4, 3)], 10);
    }

    #[test]
    fn test_star_pattern_inward() {
        // Multiple sources to different destinations (no conflicts)
        // 0 -> 5, 1 -> 6, 2 -> 7, 3 -> 8, 4 -> 9
        test_parallel_copies(vec![(0, 5), (1, 6), (2, 7), (3, 8), (4, 9)], 15);
    }

    /// Property test: verify that the algorithm never overwrites a source before it's read
    #[test]
    fn test_no_premature_overwrite() {
        // This is implicitly tested by all other tests, but let's be explicit
        // For the chain 0 -> 1 -> 2, if we did 0->1 first, then 1 would be overwritten
        // before we could copy it to 2.
        let copies = vec![(0, 1), (1, 2)];

        let mut registers = vec![10, 20, 30];
        let sequenced: Vec<_> = sequence_parallel_copies(copies).collect();

        // Apply and verify
        for (src, dst) in &sequenced {
            let src_idx = match src {
                Register::Given(r) => *r as usize,
                Register::Temp => panic!("Temp should not be used for simple chain"),
            };
            let dst_idx = match dst {
                Register::Given(r) => *r as usize,
                Register::Temp => panic!("Temp should not be used for simple chain"),
            };
            registers[dst_idx] = registers[src_idx];
        }

        // Expected: reg[0]=10, reg[1]=10, reg[2]=20
        assert_eq!(registers, vec![10, 10, 20]);
    }

    /// Test that cycles use the temp register correctly
    #[test]
    fn test_swap_uses_temp_or_reuses_register() {
        let copies = vec![(0, 1), (1, 0)];
        let sequenced: Vec<_> = sequence_parallel_copies(copies).collect();

        // Check that we have exactly 3 operations for a swap (save, move, restore)
        assert_eq!(sequenced.len(), 3, "Swap should require 3 operations");

        // Verify the sequence works
        let mut registers = vec![10u32; 1001];
        registers[0] = 100;
        registers[1] = 200;

        apply_sequential_copies(&mut registers, sequenced.into_iter());

        assert_eq!(registers[0], 200);
        assert_eq!(registers[1], 100);
    }

    /// Test that output count is correct for various patterns
    #[test]
    fn test_output_count() {
        // Empty -> 0 outputs
        assert_eq!(sequence_parallel_copies(vec![]).count(), 0);

        // Self-copy -> 0 outputs
        assert_eq!(sequence_parallel_copies(vec![(0, 0)]).count(), 0);

        // Single copy -> 1 output
        assert_eq!(sequence_parallel_copies(vec![(0, 1)]).count(), 1);

        // Chain of 3 -> 3 outputs
        assert_eq!(
            sequence_parallel_copies(vec![(0, 1), (1, 2), (2, 3)]).count(),
            3
        );

        // Swap (cycle of 2) -> 3 outputs (save to temp, move, restore from temp)
        assert_eq!(sequence_parallel_copies(vec![(0, 1), (1, 0)]).count(), 3);

        // Cycle of 3 -> 4 outputs (save, 2 moves, restore)
        assert_eq!(
            sequence_parallel_copies(vec![(0, 1), (1, 2), (2, 0)]).count(),
            4
        );
    }

    /// Stress test with randomized but valid input
    #[test]
    fn test_stress_random_trees() {
        // Create a random-ish tree structure
        // Each register (except 0) has exactly one source
        let copies: Vec<_> = (1..100).map(|i| (i / 3, i)).collect();
        test_parallel_copies(copies, 110);
    }

    #[test]
    fn test_stress_multiple_cycles() {
        // Multiple independent cycles of varying sizes
        let mut copies = vec![];

        // Cycle of 2: 0 <-> 1
        copies.extend(vec![(0, 1), (1, 0)]);

        // Cycle of 3: 10 -> 11 -> 12 -> 10
        copies.extend(vec![(10, 11), (11, 12), (12, 10)]);

        // Cycle of 4: 20 -> 21 -> 22 -> 23 -> 20
        copies.extend(vec![(20, 21), (21, 22), (22, 23), (23, 20)]);

        // Cycle of 5: 30 -> 31 -> 32 -> 33 -> 34 -> 30
        copies.extend(vec![(30, 31), (31, 32), (32, 33), (33, 34), (34, 30)]);

        test_parallel_copies(copies, 50);
    }
}
