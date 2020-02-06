/****************************************************************
 * Mutex-like lock that supports static allocation instead
 * of heap allocation.
 *
 * Copyright Alastair Reid 2020
 * SPDX-Licence-Identifier: BSD-3-Clause
 ****************************************************************/

#include <stdint.h>

struct mylock {
	volatile uint32_t v;
};

/*@

// Use this for uninitialized locks
predicate mylock_raw(struct mylock *l;) =
    l->v |-> _
    // &*& struct_mylock_padding(l)
;

predicate mylock(struct mylock *l; predicate() p);

predicate mylock_held(struct mylock *l, predicate() p, int threadId, real frac);

predicate create_mylock_ghost_arg(predicate() p) = true;

@*/

void mylock_init(struct mylock *l);
	//@ requires mylock_raw(l) &*& create_mylock_ghost_arg(?p) &*& p();
	//@ ensures mylock(l, p);

void mylock_fini(struct mylock *l);
	//@ requires mylock(l, ?p);
	//@ ensures p() &*& mylock_raw(l);

void mylock_acquire(struct mylock *l);
	//@ requires [?f]mylock(l, ?p);
	//@ ensures mylock_held(l, p, currentThread, f) &*& p();

void mylock_release(struct mylock *l);
	//@ requires mylock_held(l, ?p, currentThread, ?f) &*& p();
	//@ ensures [f]mylock(l, p);

/****************************************************************
 * End
 ****************************************************************/
