/****************************************************************
 * Atomic singly linked list (using mutex)
 *
 * Copyright Alastair Reid 2020
 * SPDX-Licence-Identifier: BSD-3-Clause
 ****************************************************************/

// Builds on top of a simple linked list structure
#include "list.c"

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
predicate_ctor list_invariant(struct list *l)() =
    l->head |-> ?head
    &*& lseg0(head, 0)
;

// A list that is currently locked.
//
// Note that it does not say anything about l->head because that
// is not accessible until you acquire the lock.
//
// Note that (unlike standard VeriFast examples), this does
// not require "malloc_block_list(l)" so it is possible to
// use this with stack-allocated and global lists.
predicate list(struct list *l;) =
    l->lock |-> ?mutex
    &*& mutex(mutex, list_invariant(l))
;

@*/

// initialize a previously allocated list object
void alist_init(struct list* l)
	//@ requires l->head |-> _ &*& l->lock |-> _;
	//@ ensures list(l);
{
	struct node *h = 0;
	l->head = h;
	//@ close create_mutex_ghost_arg(list_invariant(l));
	//@ close list_invariant(l)();
	struct mutex *m = create_mutex();
	l->lock = m;
}

// Empty a list - making it ready to deallocate
void alist_empty(struct list* l)
	//@ requires list(l);
	//@ ensures  l->head |-> _ &*& l->lock |-> _;
{
	mutex_dispose(l->lock);
	//@ open list_invariant(l)();
	list_dispose(l->head);
	l->head = 0;
}

// allocate and initialize a list object
struct list* alist_create()
	//@ requires true;
	//@ ensures list(result) &*& malloc_block_list(result);
{
	struct list* l = malloc(sizeof(struct list));
	if (l == 0) abort();
	// There are two ways of writing this function - both work
#if 1
	alist_init(l);
#else
	struct node *h = 0;
	l->head = h;
	//@ close create_mutex_ghost_arg(list_invariant(l));
	//@ close list_invariant(l)();
	struct mutex *m = create_mutex();
	l->lock = m;
#endif
	return l;
}

void alist_dispose(struct list* l)
	//@ requires list(l) &*& malloc_block_list(l);
	//@ ensures  true;
{
	mutex_dispose(l->lock);
	//@ open list_invariant(l)();
	list_dispose(l->head);
	free(l);
}

void alist_cons(struct list* l, int value)
	//@ requires list(l);
	//@ ensures  list(l);
{
	mutex_acquire(l->lock);
	//@ open list_invariant(l)();
	l->head = cons(l->head, value);
	//@ close list_invariant(l)();
	mutex_release(l->lock);
}

int alist_head(struct list* l)
	//@ requires list(l);
	//@ ensures  list(l);
{
	mutex_acquire(l->lock);
	//@ open list_invariant(l)();
	int r = l->head ? head(l->head) : -1;
	//@ close list_invariant(l)();
	mutex_release(l->lock);
	return r;
}

void alist_tail(struct list* l)
	//@ requires list(l);
	//@ ensures  list(l);
{
	mutex_acquire(l->lock);
	//@ open list_invariant(l)();
	if (l->head) {
		l->head = tail(l->head);
	}
	//@ close list_invariant(l)();
	mutex_release(l->lock);
}

// test code written using alist_create
void test_alist1()
	//@ requires true;
	//@ ensures  true;
{
	struct list *l = alist_create();
	alist_cons(l, 3);
	alist_cons(l, 4);
	int x = alist_head(l);
	alist_tail(l);
	int y = alist_head(l);
	alist_tail(l);
	// we don't track contents of list so we can't assert anything about x and y

	alist_dispose(l);
}

// test code written using list_init
void test_alist2()
	//@ requires true;
	//@ ensures  true;
{
	struct list l;
	alist_init(&l);

	alist_cons(&l, 3);
	int x = alist_head(&l);
	alist_tail(&l);

	alist_empty(&l);
}

/****************************************************************
 * End
 ****************************************************************/
