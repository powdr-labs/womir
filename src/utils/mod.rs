pub mod offset_map;
pub mod range_consolidation;
pub mod rev_vec_filler;
pub mod tree;

/// Removes the values at the given sorted indices from a Vec,
/// preserving the order of the remaining elements.
///
/// It is a little better than doing with `Vec::retain()` because
/// we can skip iterating the beginning of the vector until the
/// first index to remove.
///
/// For every removed or moved element, the callback is called with
/// the source index and destination (if any).
///
/// # Panics
///
/// Panics if `sorted_indices` is not sorted in ascending order,
/// contains duplicates or out of bounds elements.
///
/// May leak the contents of the vector on panic.
pub fn remove_indices<T>(
    vec: &mut Vec<T>,
    sorted_indices: impl IntoIterator<Item = usize>,
    mut callback: impl FnMut(usize, Option<usize>),
) {
    let mut to_remove = sorted_indices.into_iter().peekable();
    let Some(mut dest) = to_remove.next() else {
        return;
    };

    let len = vec.len();

    // Set the len 0 to avoid double drops in case of panic.
    // SAFETY: we have len tracking what part of the vec is initialized.
    unsafe {
        vec.set_len(0);
    }

    {
        let buf = &mut vec.spare_capacity_mut()[..len];

        // Poor man's borrow checker: prevents vec name from being used in this scope
        #[allow(unused_variables)]
        let vec = ();

        // Drop the first element to remove.
        unsafe {
            buf[dest].assume_init_drop();
        }
        callback(dest, None);

        let mut src = dest + 1;
        while src < len {
            let next_to_remove = to_remove.peek();
            // Sanity check that the indices are sorted and have no duplicates.
            if let Some(&next_to_remove) = next_to_remove
                && next_to_remove < src
            {
                panic!("sorted_indices must be sorted ascending with no duplicates");
            } else if next_to_remove == Some(&src) {
                // This source index is also to be removed: drop it.
                unsafe {
                    buf[src].assume_init_drop();
                }
                callback(src, None);
                to_remove.next();
            } else {
                buf[dest].write(unsafe { buf[src].assume_init_read() });
                callback(src, Some(dest));
                dest += 1;
            }
            src += 1;
        }
    }

    unsafe {
        // All the elements from `dest` have already been dropped or moved.
        vec.set_len(dest);
    }
    assert!(to_remove.next().is_none());
}
