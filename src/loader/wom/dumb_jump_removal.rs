//! This module implements a simple pass to remove dumb jumps, i.e. jumps that
//! plainly jump to the next instruction unconditionally.
//!
//! This must be done after flattening, because breaks are important to
//! generate the appropriate argument copy instructions.

use crate::loader::{settings::Settings, wom::flattening::WriteOnceAsm};

pub fn remove_dumb_jumps<'a, S: Settings<'a>>(
    s: &S,
    asm: &mut WriteOnceAsm<S::Directive>,
) -> usize {
    let mut removed = 0;

    let old_directives = std::mem::take(&mut asm.directives);
    asm.directives.reserve(old_directives.len());

    let mut old_directives = old_directives.into_iter();
    let Some(mut prev_directive) = old_directives.next() else {
        // Is it even possible for a valid function to be empty?
        return 0;
    };

    for curr_directive in old_directives {
        match S::to_plain_local_jump(prev_directive) {
            Ok(jump) => {
                if S::is_label(&curr_directive) == Some(&jump) {
                    // This is a dumb jump, don't keep it.
                    removed += 1;
                } else {
                    // Current directive is not a label matching the preceding jump,
                    // so we keep the jump.
                    asm.directives.push(s.emit_jump(jump));
                }
            }
            Err(prev_directive) => {
                // This is not a jump, keep it.
                asm.directives.push(prev_directive);
            }
        };
        prev_directive = curr_directive;
    }
    asm.directives.push(prev_directive);

    removed
}
