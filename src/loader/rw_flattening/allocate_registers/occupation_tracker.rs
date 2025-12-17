use std::{collections::BTreeMap, ops::Range};

use iset::{Entry, IntervalMap};

use crate::loader::{dag::ValueOrigin, liveness_dag::Liveness};

struct AllocationEntry {
    origin: ValueOrigin,
    reg_range: Range<u32>,
    /// Starts at the node that creates the value, ends at the last node that uses it.
    /// Since the standard Range is exclusive at the end, this works nicely to prevent
    /// overlapping when the node who consumes the value immediately produces another
    /// at the same register.
    live_range: Range<usize>,
    /// Whether this allocation doesn't live past
    ephemeral: bool,
}

/// Tracks what registers are currently occupied by what values.
pub struct OccupationTracker<'a> {
    liveness: &'a Liveness,
    alive_interval_map: IntervalMap<usize, usize>,
    origin_map: BTreeMap<ValueOrigin, usize>,
    allocations: Vec<AllocationEntry>,
}

impl<'a> OccupationTracker<'a> {
    pub fn new(liveness: &'a Liveness) -> Self {
        Self {
            liveness,
            alive_interval_map: IntervalMap::new(),
            origin_map: BTreeMap::new(),
            allocations: Vec::new(),
        }
    }

    /// Allocates the value exactly at the given register range.
    ///
    /// Returns Err if not possible (overlap with existing allocation).
    pub fn set_allocation(&mut self, origin: ValueOrigin, reg_range: Range<u32>) -> Result<(), ()> {
        let live_range = origin.node
            ..self
                .liveness
                .query_liveness(origin.node, origin.node, origin.output_idx);

        let Entry::Vacant(entry) = self.alive_interval_map.entry(live_range) else {
            return Err(());
        };

        let entry_idx = self.allocations.len();
        self.allocations.push(AllocationEntry {
            origin,
            reg_range,
            live_range: entry.interval(),
        });
        entry.insert(entry_idx);
        self.origin_map.insert(origin, entry_idx);
        Ok(())
    }

    /// Tries to allocate the value at the given register range, if not already allocated.
    /// Returns false if the value was already allocated.
    /// If not possible to allocate on hint, allocates elsewhere and returns false.
    /// Returns true if allocation happened at hint.
    pub fn try_allocate_with_hint(&mut self, origin: ValueOrigin, hint: Range<u32>) -> bool {
        todo!()
    }

    /// Allocates a value wherever there is space, if not already allocated.
    ///
    /// Returns the range allocated for the value.
    pub fn try_allocate(&mut self, origin: ValueOrigin, size: u32) -> Range<u32> {
        todo!()
    }

    /// Gets the current allocation of a value.
    pub fn get_allocation(&self, origin: ValueOrigin) -> Option<Range<u32>> {
        todo!()
    }

    /// Returns the start of a function call frame.
    ///
    /// I.e., the first register after the last allocated one at this point,
    /// so everything from there on is free for the function call.
    pub fn allocate_fn_call(&self, call_index: usize) -> u32 {
        todo!()
    }

    /// Blocks the registers occupied in the sub-tracker from being used
    /// in this tracker.
    pub fn project_from_sub_tracker(
        &mut self,
        sub_block_index: usize,
        sub_tracker: &OccupationTracker,
    ) {
        todo!()
    }

    pub fn make_sub_tracker(&self, sub_block_index: usize) -> Self {
        todo!()
    }

    /// Generates the final allocations map.
    pub fn into_allocations(self) -> BTreeMap<ValueOrigin, Range<u32>> {
        todo!()
    }
}
