use std::mem::ManuallyDrop;

/// This is a simple helper to fill a vector in reverse order.
pub struct RevVecFiller<T> {
    vec: Vec<T>,
    size: usize,
    remaining_space: usize,
}

impl<T> RevVecFiller<T> {
    pub fn new(size: usize) -> Self {
        Self {
            vec: Vec::with_capacity(size),
            size,
            remaining_space: size,
        }
    }

    pub fn try_push_front(&mut self, value: T) -> Result<(), T> {
        let idx = match self.remaining_space.checked_sub(1) {
            Some(i) => i,
            None => return Err(value),
        };

        let spare = self.vec.spare_capacity_mut();

        // Note to future editors: this block is critical.
        // Soundness: `remaining_space` must only be updated *after* the slot is written.
        // If a panic occurs after the write but before updating `remaining_space`,
        // the written element may be leaked (but this remains memory-safe).
        {
            // SAFETY: while filling, `vec.len() == 0`, so `spare.len() == vec.capacity()`.
            //  Also `idx < size <= capacity`, so `idx < spare.len()`.
            unsafe { spare.get_unchecked_mut(idx) }.write(value);
            self.remaining_space = idx;
        }
        Ok(())
    }

    pub fn try_into_vec(self) -> Result<Vec<T>, ()> {
        if self.remaining_space != 0 {
            return Err(());
        }

        // We are taking ownership of self.vec, so we no longer want the
        // Drop impl to run.
        let mut me = ManuallyDrop::new(self);
        let mut vec = std::mem::take(&mut me.vec);

        // SAFETY: at this point, all elements have been initialized.
        unsafe { vec.set_len(me.size) };

        Ok(vec)
    }
}

impl<T> Drop for RevVecFiller<T> {
    fn drop(&mut self) {
        let initialized_part = &mut self.vec.spare_capacity_mut()[self.remaining_space..self.size];
        for elem in initialized_part {
            // SAFETY: we are iterating only over the initialized part.
            unsafe {
                elem.assume_init_drop();
            }
        }
    }
}
