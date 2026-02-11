use std::{iter::FusedIterator, ops::Range};

/// Iterates over the consolidated ranges of a given set of overlapping ranges.
///
/// The ranges are returned in sorted order.
pub struct RangeConsolidationIterator<T> {
    reverse_sorted_ranges: Vec<Range<T>>,
}

impl<T: Ord> RangeConsolidationIterator<T> {
    pub fn new(occupied_ranges: Vec<Range<T>>) -> Self {
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
