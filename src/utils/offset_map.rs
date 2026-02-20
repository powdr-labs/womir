use std::ops::AddAssign;

/// A map from indices to removal offsets, used to adjust indices after elements
/// have been removed from a list.
///
/// When elements are removed from an ordered list (e.g., nodes or outputs),
/// subsequent indices need to be shifted down to account for the gaps. This
/// structure records which indices were removed and efficiently computes the
/// cumulative offset (i.e., how many removals occurred at or before a given
/// index) via binary search.
///
/// # Usage
///
/// 1. Create with `OffsetMap::new()`.
/// 2. Call `append(index)` for each removed index, **in ascending order**.
/// 3. Call `get(&index)` to obtain the offset to subtract from `index`:
///    `new_index = index - offset_map.get(&index)`.
///
/// # Example
///
/// Suppose a list `[A, B, C, D, E]` (indices 0..5) and elements at indices
/// 1 and 3 are removed, yielding `[A, C, E]`:
///
/// ```text
/// let mut m = OffsetMap::new();
/// m.append(1); // removed index 1
/// m.append(3); // removed index 3
///
/// m.get(&0) == 0  // A stays at 0
/// m.get(&2) == 1  // C moves from 2 to 1
/// m.get(&4) == 2  // E moves from 4 to 2
/// ```
#[derive(Default)]
pub struct OffsetMap<K: Ord, V: PartialEq + Eq> {
    default: V,
    counter: V,
    /// Holds (removed_index, cumulative_count) pairs, sorted by index for
    /// binary search.
    map: Vec<(K, V)>,
}

impl<K: Ord + PartialEq + Eq, V: Copy + PartialEq + Eq + AddAssign<V> + From<u8>> OffsetMap<K, V> {
    pub fn new() -> Self {
        Self {
            default: 0.into(),
            counter: 0.into(),
            map: Vec::new(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Record `index` as removed. Must be called in ascending index order.
    pub fn append(&mut self, index: K) {
        if let Some((k, _)) = self.map.last() {
            // The keys must be in ascending order.
            assert!(index >= *k);
        }

        self.counter += 1.into();
        self.map.push((index, self.counter));
    }

    /// Return how many removals occurred at or before `index`.
    /// Subtract this from `index` to get the new (shifted) index.
    pub fn get(&self, index: &K) -> &V {
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
