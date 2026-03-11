use crate::loader::rwm::register_allocation::Allocation;
use crate::loader::{dag::ValueOrigin, rwm::liveness_dag::Liveness};
use crate::utils::range_consolidation::RangeConsolidationIterator;
use iset::IntervalMap;
use itertools::Itertools;
use std::collections::HashMap;
use std::io::Write;
use std::{
    collections::BTreeMap, fs::File, io::BufWriter, num::NonZeroU32, ops::Range, path::Path,
};

#[derive(Debug)]
enum AllocationType {
    FunctionFrame,
    /// Registers blocked because they are used internally in a sub-block
    SubBlockInternal,
    BlockedRegistersAtParent,
    ExplicitlyBlocked,
    // A normal value allocation
    Value {
        origin: ValueOrigin,
        do_not_relocate: bool,
    },
}

#[derive(Debug)]
struct AllocationEntry {
    kind: AllocationType,
    reg_range: Range<u32>,
    /// Starts at the node that creates the value, ends at the last node that uses it.
    /// Since the standard Range is exclusive at the end, this works nicely to prevent
    /// overlapping when the node who consumes the value immediately produces another
    /// at the same register.
    live_range: Range<usize>,
}

/// Maps occupied registers over nodes.
#[derive(Debug)]
pub struct Occupation {
    /// Maps the range where the value is alive (in nodes)
    /// to an index in the allocations vector.
    alive_interval_map: IntervalMap<usize, usize>,
    allocations: Vec<AllocationEntry>,
}

impl Occupation {
    pub fn reg_occupation(&self, live_range: Range<usize>) -> Vec<Range<u32>> {
        self.alive_interval_map
            .values(live_range)
            .map(move |entry_idx| self.allocations[*entry_idx].reg_range.clone())
            .collect_vec()
    }

    fn consolidated_reg_occupation(
        &self,
        live_range: Range<usize>,
    ) -> impl Iterator<Item = Range<u32>> {
        let occupied_ranges = self.reg_occupation(live_range);
        RangeConsolidationIterator::new(occupied_ranges)
    }
}

/// Tracks what registers are currently occupied by what values.
#[derive(Debug)]
pub struct OccupationTracker {
    liveness: Liveness,
    occupation: Occupation,
    origin_map: BTreeMap<ValueOrigin, usize>,
    call_frames: HashMap<usize, u32>,
}

impl OccupationTracker {
    pub fn new(liveness: Liveness) -> Self {
        Self {
            liveness,
            occupation: Occupation {
                alive_interval_map: IntervalMap::new(),
                allocations: Vec::new(),
            },
            origin_map: BTreeMap::new(),
            call_frames: HashMap::new(),
        }
    }

    pub fn liveness(&self) -> &Liveness {
        &self.liveness
    }

    /// Allocates the value exactly at the given register range.
    ///
    /// Warning: this function doesn't check for overlaps with other existing allocations!
    pub fn set_allocation(&mut self, origin: ValueOrigin, reg_range: Range<u32>) {
        let live_range = self.natural_liveness(origin);

        if let Some(alloc_idx) = self.origin_map.get(&origin) {
            let existing_alloc = &self.occupation.allocations[*alloc_idx];
            assert_eq!(existing_alloc.reg_range, reg_range);
        }

        self.insert(
            AllocationType::Value {
                origin,
                do_not_relocate: true,
            },
            reg_range,
            live_range,
        );
    }

    /// Reserve a given register range, blocking it from being used.
    pub fn reserve_range(&mut self, reg_range: Range<u32>) {
        let whole_range = 0..usize::MAX;
        self.insert(AllocationType::ExplicitlyBlocked, reg_range, whole_range);
    }

    /// Tries to allocate the value at the given register range, if not already allocated.
    ///
    /// If not possible to allocate on hint, allocates elsewhere and returns false.
    ///
    /// Returns if allocation happened at hint, and the liveness end if allocated at all.
    pub fn try_allocate_with_hint(
        &mut self,
        origin: ValueOrigin,
        hint: Range<u32>,
    ) -> (bool, Option<usize>) {
        match self.try_allocate_at(origin, hint.clone()) {
            TryAllocResult::AlreadyAllocated => (false, None),
            TryAllocResult::AllocatedAtHint {
                end_of_liveness, ..
            } => (true, Some(end_of_liveness)),
            TryAllocResult::NotAllocated {
                live_range,
                existing_entries,
            } => {
                // Could not allocate at hint, allocate elsewhere
                let end_of_liveness = live_range.end;
                self.allocate_where_possible(
                    origin,
                    NonZeroU32::new(hint.len() as u32).expect("size must be non-zero"),
                    live_range,
                    existing_entries,
                )
                .expect("overflow in allocation");

                (false, Some(end_of_liveness))
            }
        }
    }

    fn try_allocate_at(&mut self, origin: ValueOrigin, hint: Range<u32>) -> TryAllocResult {
        let live_range = self.natural_liveness(origin);

        if self.origin_map.contains_key(&origin) {
            return TryAllocResult::AlreadyAllocated;
        }

        let existing_entries = self.occupation.reg_occupation(live_range.clone());
        if overlaps_any(existing_entries.iter(), &hint) {
            TryAllocResult::NotAllocated {
                live_range,
                existing_entries,
            }
        } else {
            // Can allocate at hint
            let end_of_liveness = live_range.end;
            let alloc_idx = self.insert(
                AllocationType::Value {
                    origin,
                    do_not_relocate: true,
                },
                hint,
                live_range,
            );
            TryAllocResult::AllocatedAtHint {
                end_of_liveness,
                alloc_idx,
            }
        }
    }

    /// Allocates a value wherever there is space, if not already allocated.
    ///
    /// Returns the end of liveness range if allocation suceeded.
    /// Returns none if it was already allocated.
    pub fn try_allocate(&mut self, origin: ValueOrigin, size: NonZeroU32) -> Option<usize> {
        let live_range = self.natural_liveness(origin);
        let end_of_liveness = live_range.end;

        if self.origin_map.contains_key(&origin) {
            return None;
        }

        let existing_entries = self.occupation.reg_occupation(live_range.clone());
        self.allocate_where_possible(origin, size, live_range, existing_entries)
            .expect("overflow in allocation");

        Some(end_of_liveness)
    }

    /// Gets the current allocation of a value.
    pub fn get_allocation(&self, origin: ValueOrigin) -> Option<Range<u32>> {
        self.origin_map
            .get(&origin)
            .map(|idx| self.occupation.allocations[*idx].reg_range.clone())
    }

    /// Reserve the space used by a function call and allocates all the outputs
    /// that haven't been allocated yet at their natural position on the call frame.
    ///
    /// Returns the start of the call frame, i.e., the first register after the last
    /// allocated one at this point, so everything from there on is free for the
    /// function call.
    pub fn allocate_fn_call(
        &mut self,
        call_index: usize,
        output_sizes: impl Iterator<Item = u32>,
        number_of_saved_copies: &mut usize,
    ) -> u32 {
        // For the frame start, find the highest allocated register at this point,
        // excluding the outputs of this call itself, that may already be allocated
        // and can overlap with the call frame, since they are only produced at the
        // end of the call.
        let frame_start = self
            .occupation
            .alive_interval_map
            .values_overlap(call_index)
            .filter_map(|entry_idx| {
                let alloc = &self.occupation.allocations[*entry_idx];
                if let AllocationType::Value { origin, .. } = alloc.kind
                    && origin.node == call_index
                {
                    // This is an output of the call itself, ignore it.
                    None
                } else {
                    Some(alloc.reg_range.end)
                }
            })
            .max()
            .unwrap_or(0);

        self.call_frames.insert(call_index, frame_start);

        // If an output is already allocated, and the placement was not
        // explicitly requested, and it is not at its natural position,
        // we remove it so we can try to relocate it at its natural position,
        // to avoid unnecessary copies.
        //
        // If it was explicitly requested, we keep it there, because the value
        // will be needed at that register anyway, so a copy is unavoidable.
        //
        // If the output is not allocated, it means it is not used, and its
        // liveness must be the current node only. In this case, we also allocate
        // at its natural position. It will not clobber any other allocation
        // because it will expire immediately.
        let mut to_rellocate = Vec::new();
        let mut accumulated_offset = frame_start;
        for (output_idx, size) in output_sizes.enumerate() {
            let origin = ValueOrigin {
                node: call_index,
                output_idx: output_idx as u32,
            };
            let natural_range = accumulated_offset..(accumulated_offset + size);

            if let Some(alloc_idx) = self.origin_map.get(&origin) {
                let alloc = &self.occupation.allocations[*alloc_idx];
                if alloc.reg_range != natural_range
                    && !matches!(
                        alloc.kind,
                        AllocationType::Value {
                            do_not_relocate: true,
                            ..
                        }
                    )
                {
                    // Maybe this output can be relocated at its natural position.
                    to_rellocate.push(OutputForRelocations {
                        output_idx: origin.output_idx,
                        natural_range,
                        original_range: alloc.reg_range.clone(),
                    });
                    self.remove(*alloc_idx);
                }
            } else {
                // Output was not allocated yet, allocate it at its natural position
                let live_range = self.natural_liveness(origin);
                assert_eq!(
                    live_range.len(),
                    1,
                    "unused function output should have one node liveness"
                );

                self.insert(
                    AllocationType::Value {
                        origin,
                        do_not_relocate: true,
                    },
                    natural_range,
                    live_range,
                );
            }

            accumulated_offset += size;
        }

        // Relocate the outputs that can be relocated at their natural position.
        *number_of_saved_copies += self.relocate_fn_call_outputs(call_index, to_rellocate);

        // Reserve the entire remaining space for the function frame.
        // May overlap with some unused function outputs, but that is fine.
        let function_range = frame_start..u32::MAX;

        self.insert(
            AllocationType::FunctionFrame,
            function_range,
            call_index..(call_index + 1),
        );

        frame_start
    }

    pub fn mark_as_fixed(&mut self, origin: &ValueOrigin) {
        let alloc_idx = self.origin_map[origin];
        if let AllocationType::Value {
            do_not_relocate, ..
        } = &mut self.occupation.allocations[alloc_idx].kind
        {
            *do_not_relocate = true;
        } else {
            unreachable!();
        }
    }

    /// Tries to place the outputs of a function call at their natural
    /// position on the call frame.
    fn relocate_fn_call_outputs(
        &mut self,
        call_index: usize,
        mut to_rellocate: Vec<OutputForRelocations>,
    ) -> usize {
        // The algorithm is a bit triky, because in some rare (hopefully)
        // ocasions, the full relocation might fail. So we must clear our
        // relocation attempt, restore the failing entry to its original state
        // (that we know to be valid), remove the offending entry from the set
        // of outputs to relocate, and retry.
        //
        // Since every fail removes one entry from the set of outputs to relocate,
        // this terminates.
        let mut new_allocs = vec![None; to_rellocate.len()];

        'retry: loop {
            let mut copies_saved = 0;

            // First, try to set all the allocations at their natural position.
            // Some might fail because of overlaps with other allocations, but
            // that is fine.
            for (entry_idx, entry) in to_rellocate.iter().enumerate() {
                let result = self.try_allocate_at(
                    ValueOrigin {
                        node: call_index,
                        output_idx: entry.output_idx,
                    },
                    entry.natural_range.clone(),
                );

                match result {
                    TryAllocResult::AlreadyAllocated => unreachable!(),
                    TryAllocResult::NotAllocated { .. } => {
                        // We try allocating later, so this doesn't block the natural
                        // placement of the other outputs.
                    }
                    TryAllocResult::AllocatedAtHint { alloc_idx, .. } => {
                        // Allocated at natural position, great!
                        new_allocs[entry_idx] = Some(alloc_idx);
                        copies_saved += entry.original_range.len();
                    }
                }
            }

            // Allocate the remaining wherever possible
            for (entry_idx, entry) in to_rellocate.iter().enumerate() {
                if new_allocs[entry_idx].is_some() {
                    continue;
                }

                let origin = ValueOrigin {
                    node: call_index,
                    output_idx: entry.output_idx,
                };

                let live_range = self.natural_liveness(origin);
                let existing_entries = self.occupation.reg_occupation(live_range.clone());
                if let Ok(alloc_idx) = self.allocate_where_possible(
                    origin,
                    (entry.original_range.len() as u32).try_into().unwrap(),
                    live_range.clone(),
                    existing_entries,
                ) {
                    new_allocs[entry_idx] = Some(alloc_idx);
                } else {
                    // Relocation failed!
                    //
                    // Clear our allocation attempt, restore the failing entry and remove it
                    // from the set of outputs to relocate.
                    for alloc_idx in new_allocs.iter().flatten() {
                        self.remove(*alloc_idx);
                    }

                    self.set_allocation(origin, entry.original_range.clone());

                    to_rellocate.swap_remove(entry_idx);
                    new_allocs.truncate(to_rellocate.len());
                    new_allocs.fill(None);

                    continue 'retry;
                }
            }

            // If we got here, it means all entries were relocated successfully, we are done.
            break copies_saved;
        }
    }

    /// Creates a new occupation tracker, with all the allocations crossing the given
    /// sub-block index expanded into the sub-tracker, so that those slots are blocked from
    /// being used in the sub-tracker.
    pub fn make_sub_tracker(&self, sub_block_index: usize, sub_liveness: Liveness) -> Self {
        let mut sub_tracker = OccupationTracker::new(sub_liveness);

        let sub_range = sub_block_index..(sub_block_index + 1);
        let sub_occupation = self.occupation.consolidated_reg_occupation(sub_range);

        let whole_range = 0..usize::MAX;
        for reg_range in sub_occupation {
            sub_tracker.insert(
                AllocationType::BlockedRegistersAtParent,
                reg_range,
                whole_range.clone(),
            );
        }
        sub_tracker
    }

    /// Blocks the registers occupied in the sub-tracker from being used
    /// in this tracker.
    pub fn project_from_sub_tracker(
        &mut self,
        sub_block_index: usize,
        sub_tracker: &OccupationTracker,
    ) {
        let projection = sub_tracker
            .occupation
            .allocations
            .iter()
            .filter_map(|alloc| match alloc.kind {
                AllocationType::BlockedRegistersAtParent => None,
                _ => Some(alloc.reg_range.clone()),
            })
            .collect_vec();

        for alloc in RangeConsolidationIterator::new(projection) {
            self.insert(
                AllocationType::SubBlockInternal,
                alloc,
                sub_block_index..(sub_block_index + 1),
            );
        }
    }

    /// Generates the final allocations map.
    pub fn into_allocations(self, labels: HashMap<u32, usize>) -> Allocation {
        let mut nodes_outputs = BTreeMap::new();
        for alloc in &self.occupation.allocations {
            if let AllocationType::Value { origin, .. } = alloc.kind {
                nodes_outputs.insert(origin, alloc.reg_range.clone());
            }
        }
        Allocation {
            nodes_outputs,
            occupation: self.occupation,
            labels,
            call_frames: self.call_frames,
        }
    }

    pub fn _dump(&self, path: &Path) {
        let mut file =
            BufWriter::new(File::create(path).expect("could not create allocation dump file"));
        for (life_range, alloc) in self.occupation.alive_interval_map.unsorted_iter() {
            let alloc = &self.occupation.allocations[*alloc];

            let ty = match &alloc.kind {
                AllocationType::FunctionFrame => 'U',
                AllocationType::SubBlockInternal => 'S',
                AllocationType::BlockedRegistersAtParent => 'B',
                AllocationType::ExplicitlyBlocked => 'E',
                AllocationType::Value { .. } => 'A',
            };
            writeln!(
                file,
                "{ty} {} {} {} {}",
                life_range.start,
                alloc.reg_range.start,
                life_range.end - 1,
                alloc.reg_range.end - 1
            )
            .expect("could not write allocation dump");
        }
    }

    fn allocate_where_possible(
        &mut self,
        origin: ValueOrigin,
        size: NonZeroU32,
        live_range: Range<usize>,
        existing_entries: Vec<Range<u32>>,
    ) -> Result<usize, ()> {
        // Track the end of the current occupied space
        let mut curr_end = 0;

        for r in RangeConsolidationIterator::new(existing_entries) {
            let gap_size = r.start.saturating_sub(curr_end);
            if gap_size >= size.get() {
                // Found a gap that fits: [curr_end, r.start)
                break;
            }
            curr_end = r.end;
        }

        // Allocate at the first gap found (or at the end).
        let alloc = curr_end..(curr_end.checked_add(size.get()).ok_or(())?);
        Ok(self.insert(
            AllocationType::Value {
                origin,
                do_not_relocate: false,
            },
            alloc,
            live_range,
        ))
    }

    fn insert(
        &mut self,
        kind: AllocationType,
        reg_range: Range<u32>,
        live_range: Range<usize>,
    ) -> usize {
        let entry_idx = self.occupation.allocations.len();
        if let AllocationType::Value { origin, .. } = kind {
            self.origin_map.insert(origin, entry_idx);
        }

        // Force insert because live ranges are not unique.
        self.occupation
            .alive_interval_map
            .force_insert(live_range.clone(), entry_idx);

        self.occupation.allocations.push(AllocationEntry {
            kind,
            reg_range,
            live_range,
        });
        entry_idx
    }

    fn remove(&mut self, entry_idx: usize) {
        // Remove the entry itself
        let alloc = self.occupation.allocations.swap_remove(entry_idx);

        // Remove the entry from the two indices
        if let AllocationType::Value { origin, .. } = alloc.kind {
            self.origin_map.remove(&origin);
        }
        self.occupation
            .alive_interval_map
            .remove_where(alloc.live_range.clone(), |idx| *idx == entry_idx);

        // Now we need to fix the references to the entry moved by swap_remove.
        let old_idx = self.occupation.allocations.len();
        if entry_idx == old_idx {
            // We removed the last entry, no need to fix anything.
            return;
        }

        let moved_entry = &self.occupation.allocations[entry_idx];
        if let AllocationType::Value { origin, .. } = moved_entry.kind {
            *self.origin_map.get_mut(&origin).unwrap() = entry_idx;
        }

        self.occupation
            .alive_interval_map
            .remove_where(moved_entry.live_range.clone(), |idx| *idx == old_idx);
        self.occupation
            .alive_interval_map
            .force_insert(moved_entry.live_range.clone(), entry_idx);
    }

    fn natural_liveness(&self, origin: ValueOrigin) -> Range<usize> {
        let range = origin.node
            ..self
                .liveness
                .query_liveness(origin.node, origin.node, origin.output_idx);

        // Zero-length live ranges are valid (values that are never used), but not supported
        // by iset::IntervalMap, so we extend them by one (pretend they are used at the next
        // node). This should have no practical effect.
        if range.start == range.end {
            range.start..(range.end + 1)
        } else {
            range
        }
    }
}

enum TryAllocResult {
    AlreadyAllocated,
    AllocatedAtHint {
        end_of_liveness: usize,
        alloc_idx: usize,
    },
    NotAllocated {
        live_range: Range<usize>,
        existing_entries: Vec<Range<u32>>,
    },
}

struct OutputForRelocations {
    output_idx: u32,
    original_range: Range<u32>,
    natural_range: Range<u32>,
}

fn overlaps_any<'a, T>(mut set: impl Iterator<Item = &'a Range<T>>, target: &Range<T>) -> bool
where
    T: Ord + Copy + 'a,
{
    set.any(|range| ranges_intersection(range, target).is_some())
}

fn ranges_intersection<T>(range_a: &Range<T>, range_b: &Range<T>) -> Option<Range<T>>
where
    T: Ord + Copy,
{
    let start = if range_a.start > range_b.start {
        range_a.start
    } else {
        range_b.start
    };
    let end = if range_a.end < range_b.end {
        range_a.end
    } else {
        range_b.end
    };
    if start < end { Some(start..end) } else { None }
}
