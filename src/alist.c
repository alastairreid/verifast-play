/****************************************************************
 * Atomic singly linked list (using mutex)
 *
 * Copyright Alastair Reid 2020
 * SPDX-Licence-Identifier: BSD-3-Clause
 ****************************************************************/

// Builds on top of a simple linked list structure
#include "list.h"

#include "stdlib.h"
#include "threading.h"

// A linked list using a lock to ensure atomic updates
struct list {
	struct node*  head;
	struct mutex* lock;
};

/*@

// Invariant for a list object that should hold whenever the list
// is locked.
//
// Note that it does not mention the mutex itself because that
// would require a cyclic reference to this invariant
predicate_ctor alist_invariant(struct list *l)() =
    l->head |-> ?head
    &*& list(head)
;

// A list that is currently locked.
//
// Note that it does not say anything about l->head because that
// is not accessible until you acquire the lock.
//
// Note that (unlike standard VeriFast examples), this does
// not require "malloc_block_list(l)" so it is possible to
// use this with stack-allocated and global lists.
predicate alist(struct list *l;) =
    l->lock |-> ?mutex
    &*& mutex(mutex, alist_invariant(l))
;

@*/

// initialize a previously allocated list object
void alist_init(struct list* l)
	//@ requires l->head |-> _ &*& l->lock |-> _;
	//@ ensures alist(l);
{
	struct node *h = 0;
	l->head = h;
	//@ close create_mutex_ghost_arg(alist_invariant(l));
	//@ close alist_invariant(l)();
	struct mutex *m = create_mutex();
	l->lock = m;
}

// finalize a list - making it ready to deallocate
void alist_fini(struct list* l)
	//@ requires alist(l);
	//@ ensures  l->head |-> _ &*& l->lock |-> _;
{
	mutex_dispose(l->lock);
	//@ open alist_invariant(l)();
	list_dispose(l->head);
}

// allocate and initialize a list object
struct list* alist_create()
	//@ requires true;
	//@ ensures alist(result) &*& malloc_block_list(result);
{
	struct list* l = malloc(sizeof(struct list));
	if (l == 0) abort();
	// There are two ways of writing this function - both work
#if 1
	alist_init(l);
#else
	struct node *h = 0;
	l->head = h;
	//@ close create_mutex_ghost_arg(alist_invariant(l));
	//@ close alist_invariant(l)();
	struct mutex *m = create_mutex();
	l->lock = m;
#endif
	return l;
}

void alist_dispose(struct list* l)
	//@ requires alist(l) &*& malloc_block_list(l);
	//@ ensures  true;
{
	// There are two ways of writing this function - both work
#if 1
	alist_fini(l);
#else
	mutex_dispose(l->lock);
	//@ open alist_invariant(l)();
	list_dispose(l->head);
#endif
	free(l);
}

void alist_cons(int value, struct list* l)
	//@ requires [?f]alist(l);
	//@ ensures  [f]alist(l);
{
	mutex_acquire(l->lock);
	//@ open alist_invariant(l)();
	l->head = cons(value, l->head);
	//@ close alist_invariant(l)();
	mutex_release(l->lock);
}

int alist_head(struct list* l)
	//@ requires [?f]alist(l);
	//@ ensures  [f]alist(l);
{
	mutex_acquire(l->lock);
	//@ open alist_invariant(l)();
	int r = l->head ? head(l->head) : -1;
	//@ close alist_invariant(l)();
	mutex_release(l->lock);
	return r;
}

void alist_tail(struct list* l)
	//@ requires [?f]alist(l);
	//@ ensures  [f]alist(l);
{
	mutex_acquire(l->lock);
	//@ open alist_invariant(l)();
	if (l->head) {
		l->head = tail(l->head);
	}
	//@ close alist_invariant(l)();
	mutex_release(l->lock);
}

/****************************************************************
 * Sequential tests
 ****************************************************************/

// sequential test code written using alist_create
void test_alist1()
	//@ requires true;
	//@ ensures  true;
{
	struct list *l = alist_create();
	alist_cons(3, l);
	alist_cons(4, l);
	int x = alist_head(l);
	alist_tail(l);
	int y = alist_head(l);
	alist_tail(l);
	// we don't track contents of list so we can't assert anything about x and y

	alist_dispose(l);
}

// sequential test code written using list_init
void test_alist2()
	//@ requires true;
	//@ ensures  true;
{
	struct list l;
	alist_init(&l);

	alist_cons(3, &l);
	int x = alist_head(&l);
	alist_tail(&l);

	alist_fini(&l);
}

/****************************************************************
 * Concurrent tests
 ****************************************************************/

/*@

predicate_family_instance thread_run_pre(test_thread)(struct list *l, any info) = [1/2]alist(l);
predicate_family_instance thread_run_post(test_thread)(struct list *l, any info) = [1/2]alist(l);

@*/

void test_thread(struct list *l) //@ : thread_run_joinable
	//@ requires thread_run_pre(test_thread)(l, ?info);
	//@ ensures thread_run_post(test_thread)(l, info);
{
	//@ open thread_run_pre(test_thread)(l, info);
	alist_cons(3, l);
	//@ close thread_run_post(test_thread)(l, info);
}

struct thread *start_thread(struct list *l)
	//@ requires [1/2]alist(l);
	//@ ensures thread(result, test_thread, l, _);
{
	//@ close thread_run_pre(test_thread)(l, unit);
	return thread_start_joinable(test_thread, l);
}

void join_thread(struct thread *t)
	//@ requires thread(t, test_thread, ?l, _);
	//@ ensures  [1/2]alist(l);
{
	thread_join(t);
	//@ open thread_run_post(test_thread)(l, _);
}

// concurrent test code written using alist_create
void test_alist3()
	//@ requires true;
	//@ ensures  true;
{
	struct list *l = alist_create();
	struct thread *t1 = start_thread(l);
	struct thread *t2 = start_thread(l);
	join_thread(t1);
	join_thread(t2);
	alist_dispose(l);
}

// concurrent test code written using alist_init
void test_alist4()
	//@ requires true;
	//@ ensures  true;
{
	struct list l;
	alist_init(&l);
	struct thread *t1 = start_thread(&l);
	struct thread *t2 = start_thread(&l);
	join_thread(t1);
	join_thread(t2);
	alist_fini(&l);
}

/****************************************************************
 * End
 ****************************************************************/
