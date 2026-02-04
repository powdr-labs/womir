use crate::loader::rwm::register_allocation::Allocation;
use crate::loader::{dag::ValueOrigin, rwm::liveness_dag::Liveness};
use iset::IntervalMap;
use itertools::Itertools;
use std::collections::HashMap;
use std::io::Write;
use std::{
    collections::BTreeMap, fs::File, io::BufWriter, iter::FusedIterator, num::NonZeroU32,
    ops::Range, path::Path,
};

#[derive(Debug)]
enum AllocationType {
    FunctionFrame,
    /// Registers blocked because they are used internally in a sub-block
    SubBlockInternal,
    BlockedRegistersAtParent,
    ExplicitlyBlocked,
    // A normal value allocation
    Value(ValueOrigin),
}

#[derive(Debug)]
struct AllocationEntry {
    kind: AllocationType,
    /// Starts at the node that creates the value, ends at the last node that uses it.
    /// Since the standard Range is exclusive at the end, this works nicely to prevent
    /// overlapping when the node who consumes the value immediately produces another
    /// at the same register.
    reg_range: Range<u32>,
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
    fn reg_occupation(&self, live_range: Range<usize>) -> Vec<Range<u32>> {
        self.alive_interval_map
            .values(live_range)
            .map(move |entry_idx| self.allocations[*entry_idx].reg_range.clone())
            .collect_vec()
    }

    pub fn consolidated_reg_occupation(
        &self,
        live_range: Range<usize>,
    ) -> impl Iterator<Item = Range<u32>> {
        let occupied_ranges = self.reg_occupation(live_range);
        RangeConsolidationIterator::new(occupied_ranges)
    }
}

/// Tracks what registers are currently occupied by what values.
pub struct OccupationTracker {
    liveness: Liveness,
    occupation: Occupation,
    origin_map: BTreeMap<ValueOrigin, usize>,
    call_frames: HashMap<usize, u32>,
}

/// Iterates over the consolidated ranges of a given set of overlapping ranges.
struct RangeConsolidationIterator<T> {
    reverse_sorted_ranges: Vec<Range<T>>,
}

impl<T: Ord> RangeConsolidationIterator<T> {
    fn new(occupied_ranges: Vec<Range<T>>) -> Self {
        let mut reverse_sorted_ranges = occupied_ranges;
        reverse_sorted_ranges.sort_unstable_by(|a, b| b.start.cmp(&a.start));
        Self {
            reverse_sorted_ranges,
        }
    }
}

impl<T: Ord> Iterator for RangeConsolidationIterator<T> {
    type Item = Range<T>;

    fn next(&mut self) -> Option<Self::Item> {
        let mut curr = self.reverse_sorted_ranges.pop()?;

        while let Some(next) = self.reverse_sorted_ranges.last() {
            if next.start <= curr.end {
                // Overlaps/adjacent: extend current range
                let next = self.reverse_sorted_ranges.pop().unwrap();
                curr.end = curr.end.max(next.end);
            } else {
                break;
            }
        }
        Some(curr)
    }
}

impl<T: Ord> FusedIterator for RangeConsolidationIterator<T> {}

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

        self.insert(AllocationType::Value(origin), reg_range, live_range);
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
        let live_range = self.natural_liveness(origin);

        if self.origin_map.contains_key(&origin) {
            return (false, None);
        }

        let end_of_liveness = Some(live_range.end);
        let existing_entries = self.occupation.reg_occupation(live_range.clone());
        (
            if overlaps_any(existing_entries.iter(), &hint) {
                // Cannot allocate at hint, allocate elsewhere
                self.allocate_where_possible(
                    origin,
                    NonZeroU32::new(hint.len() as u32).expect("size must be non-zero"),
                    live_range,
                    existing_entries,
                );
                false
            } else {
                // Can allocate at hint
                self.insert(AllocationType::Value(origin), hint, live_range);
                true
            },
            end_of_liveness,
        )
    }

    /// Allocates a value wherever there is space, if not already allocated.
    ///
    /// Returns the end of liveness range if the value was allocated.
    pub fn try_allocate(&mut self, origin: ValueOrigin, size: NonZeroU32) -> Option<usize> {
        let live_range = self.natural_liveness(origin);
        let end_of_liveness = live_range.end;

        if self.origin_map.contains_key(&origin) {
            return None;
        }

        let existing_entries = self.occupation.reg_occupation(live_range.clone());
        self.allocate_where_possible(origin, size, live_range, existing_entries);

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
    ) -> u32 {
        // Find the highest allocated register at this point
        let frame_start = self
            .occupation
            .alive_interval_map
            .values_overlap(call_index)
            .map(|entry_idx| {
                let alloc = &self.occupation.allocations[*entry_idx];
                alloc.reg_range.end
            })
            .max()
            .unwrap_or(0);

        self.call_frames.insert(call_index, frame_start);

        // Either an output is already allocated, or it is not used, and its
        // liveness must be the current node only.
        let mut accumulated_offset = frame_start;
        for (output_idx, size) in output_sizes.enumerate() {
            let origin = ValueOrigin {
                node: call_index,
                output_idx: output_idx as u32,
            };
            if !self.origin_map.contains_key(&origin) {
                // Output was not allocated yet, allocate it at its natural position
                let live_range = self.natural_liveness(origin);
                assert_eq!(
                    live_range.len(),
                    1,
                    "unused function output should have one node liveness"
                );

                let reg_range = accumulated_offset..(accumulated_offset + size);
                self.insert(AllocationType::Value(origin), reg_range, live_range);
            }

            accumulated_offset += size;
        }

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
            if let AllocationType::Value(origin) = alloc.kind {
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

    pub fn dump(&self, path: &Path) {
        let mut file =
            BufWriter::new(File::create(path).expect("could not create allocation dump file"));
        for (life_range, alloc) in self.occupation.alive_interval_map.unsorted_iter() {
            let alloc = &self.occupation.allocations[*alloc];

            let ty = match &alloc.kind {
                AllocationType::FunctionFrame => 'U',
                AllocationType::SubBlockInternal => 'S',
                AllocationType::BlockedRegistersAtParent => 'B',
                AllocationType::ExplicitlyBlocked => 'E',
                AllocationType::Value(_) => 'A',
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
    ) {
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
        let alloc = curr_end
            ..(curr_end
                .checked_add(size.get())
                .expect("overflow in allocation"));
        self.insert(AllocationType::Value(origin), alloc, live_range);
    }

    fn insert(&mut self, kind: AllocationType, reg_range: Range<u32>, live_range: Range<usize>) {
        let entry_idx = self.occupation.allocations.len();
        if let AllocationType::Value(origin) = kind {
            self.origin_map.insert(origin, entry_idx);
        }
        self.occupation
            .allocations
            .push(AllocationEntry { kind, reg_range });
        // Force insert because live ranges are not unique.
        self.occupation
            .alive_interval_map
            .force_insert(live_range, entry_idx);
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
