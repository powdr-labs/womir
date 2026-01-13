This is a calling convention proposal for "stacked read-write infinite registers" execution model.

The frame of a function is contained inside the caller's frame (which is infinite).
The caller is responsible for choosing where the new function frame starts.

The new frame starts with the "interface" section, of size `MAX(num input words, num output words) + 2`.
The sequence of allocated slots are:

- input/output words;
- caller's return address (`RA`) and frame pointer (`FP`);
- function's local frame data, which might hold the frame for other functions called by this new function.

When a function returns, the "interface" section will contain the values returned by the function,
from where the caller can read them.

So, if a function has 3 words inputs and 1 word output, we get:

 | FP offset | Role                          |
 |-----------|-------------------------------|
 | 0         | input word 0 + output word 0  |
 | 1         | input word 1                  |
 | 2         | input word 2                  |
 | 3         | caller's return address       |
 | 4         | caller's frame pointer        |
 | 5...      | function local frame data     |

Similarly, if there are 2 word inputs and 3 word outputs, we get:

 | FP offset | Role                          |
 |-----------|-------------------------------|
 | 0         | input word 0 + output word 0  |
 | 1         | input word 1 + output word 1  |
 | 2         | output word 2                 |
 | 3         | caller's return address       |
 | 4         | caller's frame pointer        |
 | 5...      | function local frame data     |

The way a function call happens is this:

- the caller chooses a `FP` offset where the callee frame will start at the end of its own frame, i.e. after the last offset that must not be
  overwritten by the callee execution, because the callee's frame might grow indefinitely;
- based on the type of the function call, the caller copies the inputs, starting at the offset it chose in the previous step;
- the caller issues the `CALL` instruction, passing as argument the offset for the callee frame start and the offset, relative to the callee frame start,
  where the caller's `RA` and `FP` are to be stored;
- the `CALL` instruction sets up the callee frame pointer, saves the caller's `RA` and `FP` at the specified offset, and jumps to the callee code.
- when the callee must return, it issues the `RET` instruction, passing as argument the offset where the caller's `RA` and `FP` are stored;
- the `RET` instruction restores the caller's `FP` and jumps to the return address stored in the callee frame.
- the caller can then read the output words from same offset where it wrote the input words.

Two alternatives were considered, which have trade-offs, but it is not clear if they are better overall:

1) In the scheme proposed, the input and output slots are overlapping, so a function must necessarily overwrite some of the inputs with the outputs.
   The alternative would be to use separated slots for inputs and outputs, which might save a few register copies at expense of more frame memory
   being used, especially if it is part of the convention that input words must not be overwritten, thus the caller may be able to keep reading from
   the variable in following operations.
2) In this scheme, `RA` and `FP` are stored after the input/output slots. The alternative would be to store them before the input/output slots, which
   would make their location a fixed offset from `FP` (0 and 1), with the advantage that it would allow us to omit passing their location as argument
   to `CALL` and `RET` instructions. The drawback is that, after the function returns, these slots would leave a hole in the caller frame just before the
   function's output, potentially using a little more memory, if the caller could not reuse these slots for other purposes.
