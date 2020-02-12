# VeriFast Play

Experiments in using [VeriFast verification tool](https://github.com/verifast/verifast).

These are mostly just explorations of the tool but I am making them available
in case they are useful to others.
(You will be better served by running through the excellent
[VeriFast tutorial](https://people.cs.kuleuven.be/~bart.jacobs/verifast/tutorial.pdf)
if you have not already done so.)

I mostly explore this code using the VeriFast the IDE but I am including
a Makefile so that I can run regression tests on them.

Similar (possibly better) worked examples of OS kernel-like code:

- [verifast/examples/helloproc](https://github.com/verifast/verifast/blob/master/examples/helloproc/vf_README.txt)
  (all files in the same directory as that file)

## Setup

Download and install a recent [VeriFast
release](https://github.com/verifast/verifast/releases)

    wget https://github.com/verifast/verifast/releases/download/19.12/verifast-19.12-macos.tar.gz
    tar xf verifast-19.12-macos.tar.gz
    ln -s verifast-19.12 verifast
    # make binaries in release executable on recent MacOS versions
    xattr -r -d com.apple.quarantine verifast

## Test

All the examples can be checked with this command

    make check

## Overview

[Warning: I am likely to forget to update this – you might want to [explore the source directly](src).]

Current examples (all in the [src](src) directory)

- list.c – singly linked list.

  The standard list definition. Included so that it can be reused in other
  examples.

- alist.c - atomic linked list using a mutex.

  The challenge here is that I wanted the mutex to be part of the
  object it protects.

- mylock.h and locktest.c - locks that can be stack/statically-allocated.

  The challenge here is tweaking the standard mutex definition to allow
  locks that are not allocated on the heap.

- wrap.h and wraptest.c - wrapping arithmetic library.

  The challenge here is that VeriFast doesn't seem to be very good at reasoning
  about wrapping integer operations so, to help it out, I carefully implemented
  'wrap_add64' and 'wrap_sub64' that perform wrapping addition and subtraction
  without any intermediate overflow.

- padding.c - casting between types of different sizes.

  The challenge here is that the objects have to be padded with extra space
  and, when we cast from one to the other, we have to use 'open_struct' and 'chars_join'
  to convert the object plus its padding back to raw memory and then
  use 'chars_split' and 'close_struct' to convert raw memory back to an object
  plus some padding.

- align.c - reasoning about alignment of objects

  The challenge here is saying that a pointer has to be aligned.
  By itself, this seems to be easy but what is hard is that VeriFast does not
  support "alignas" or "alignof" so, instead of saying that a global
  variable has some alignment at the place where it is declared, every
  use of that global has to add an assumption that it is aligned.

- malloc0.c - a simplistic memory allocator.

  The challenge here is slicing an object off the front of a contiguous block
  of memory and converting it to a struct.

- malloc1.c and malloctest.c - a memory allocator that supports free

  The challenge here is that entries on the freelist have been padded out to
  some larger size and we have to use the techniques in padding.c to
  convert between the two views.
