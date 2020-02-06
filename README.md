# VeriFast Play

Experiments in using [VeriFast verification tool](https://github.com/verifast/verifast).

These are mostly just explorations of the tool but I am making them available
in case they are useful to others.
(You will be better served by running through the excellent
[VeriFast tutorial](https://people.cs.kuleuven.be/~bart.jacobs/verifast/tutorial.pdf)
if you have not already done so.)

I mostly explore this code using the VeriFast the IDE but I am including
a Makefile so that I can run regression tests on them.

## Setup

Download and install a recent [VeriFast
release](https://github.com/verifast/verifast/releases)

    wget https://github.com/verifast/verifast/releases/download/19.12/verifast-19.12-macos.tar.gz
    tar xf verifast-19.12-macos.tar.gz
    ln -s verifast-19.12 verifast
    # make binaries in release executable on recent MacOS versions
    xattr -r -d com.apple.quarantine verifast

## Test

todo: create a Makefile to run it all in batch mode

## Overview

[Warning: I am likely to forget to update this – you might want to [explore the source directly](src).]

Current examples (all in the [src](src) directory)

- list.c – singly linked list
- alist.c - atomic linked list
