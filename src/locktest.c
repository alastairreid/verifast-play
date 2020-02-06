/****************************************************************
 * Using locks
 *
 * Copyright Alastair Reid 2020
 * SPDX-Licence-Identifier: BSD-3-Clause
 ****************************************************************/

#include "prelude.h"
#include "mylock.h"
#include "threading.h"

// A container for some data with atomic update
// (The update is not interesting - just something I can write
// an invariant for.)
struct pair {
	int a;
	int b;
	struct mylock lock;
};

/*@

// Use this for uninitialized pairs
predicate pair_raw(struct pair *p;) =
    p->a |-> _
    &*& p->b |-> _
    &*& mylock_raw(&p->lock)
    // &*& struct_pair_padding(p)
;

// Invariant for a pair that should hold whenever the pair is locked
// is locked.
//
// Note that it does not mention the lock itself because that
// would require a cyclic reference to this invariant
predicate_ctor pair_invariant(struct pair *p)() =
    p->a |-> ?a
    &*& p->b |-> ?b
    &*& a < b
;

// A pair that is currently locked.
//
// Note that it does not say anything about l->a or l->b because
// they are not accessible until you acquire the lock.
//
// Note that (unlike standard VeriFast examples), this does
// not require "malloc_block_pair(l)" so it is possible to
// use this with stack-allocated and global paires.
predicate pair(struct pair *p;) =
    mylock(&p->lock, pair_invariant(p))
;

@*/

// initialize a previously allocated pair object
void pair_init(struct pair* p)
	//@ requires pair_raw(p);
	//@ ensures pair(p);
{
	p->a = 0;
	p->b = 10;
	//@ close create_mylock_ghost_arg(pair_invariant(p));
	//@ close pair_invariant(p)();
	mylock_init(&p->lock);
}

// finalize a pair - making it ready to deallocate
void pair_fini(struct pair* p)
	//@ requires pair(p);
	//@ ensures  pair_raw(p);
{
	mylock_fini(&p->lock);
	//@ open pair_invariant(p)();
}

void pair_inc(struct pair* p)
	//@ requires [?f]pair(p);
	//@ ensures  [f]pair(p);
{
	mylock_acquire(&p->lock);
	//@ open pair_invariant(p)();
	p->a++;
	if (p->a == p->b) {
		p->a = p->b - 1;
	}
	//@ close pair_invariant(p)();
	mylock_release(&p->lock);
}

/****************************************************************
 * Sequential tests
 ****************************************************************/

// Sequential test code
void test_pair_sequential()
	//@ requires true;
	//@ ensures  true;
{
	struct pair p;
	pair_init(&p);
	pair_inc(&p);
	pair_inc(&p);
	pair_inc(&p);
	pair_fini(&p);
}


/****************************************************************
 * Concurrent tests
 ****************************************************************/

/*@

predicate_family_instance thread_run_pre(test_thread)(struct pair *p, any info) = [1/4]pair(p);
predicate_family_instance thread_run_post(test_thread)(struct pair *p, any info) = [1/4]pair(p);

@*/

void test_thread(struct pair *p) //@ : thread_run_joinable
	//@ requires thread_run_pre(test_thread)(p, ?info);
	//@ ensures thread_run_post(test_thread)(p, info);
{
	//@ open thread_run_pre(test_thread)(p, info);
	pair_inc(p);
	//@ close thread_run_post(test_thread)(p, info);
}

struct thread *start_thread(struct pair *p)
	//@ requires [1/4]pair(p);
	//@ ensures  thread(result, test_thread, p, _);
{
	//@ close thread_run_pre(test_thread)(p, unit);
	return thread_start_joinable(test_thread, p);
}

void join_thread(struct thread *t)
	//@ requires thread(t, test_thread, ?p, _);
	//@ ensures  [1/4]pair(p);
{
	thread_join(t);
	//@ open thread_run_post(test_thread)(p, _);
}

// Concurrent test function
void test_pair_concurrent()
	//@ requires true;
	//@ ensures  true;
{
	struct pair p;
	pair_init(&p);
	struct thread *t1 = start_thread(&p);
	struct thread *t2 = start_thread(&p);
	join_thread(t1);
	join_thread(t2);
	pair_fini(&p);
}

/****************************************************************
 * End
 ****************************************************************/
