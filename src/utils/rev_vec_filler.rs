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

        // Note to future editors: ensure there is no panic possible
        // inside this block.
        {
            unsafe { spare.get_unchecked_mut(idx).write(value) };
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
        let me = ManuallyDrop::new(self);
        Ok(unsafe {
            let mut vec = std::ptr::read(&me.vec);
            vec.set_len(me.size);
            vec
        })
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
