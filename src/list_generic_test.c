/****************************************************************
 * Singly linked generic list
 *
 * Copyright Alastair Reid 2020
 * SPDX-Licence-Identifier: BSD-3-Clause
 ****************************************************************/

#include "stdlib.h"
#include "list_generic.h"

struct T {
	int value;
};

//@ predicate T(struct T* t;) = malloc_block_T(t) &*& t->value |-> ?v &*& v >= 0;

//@ predicate_family_instance Ownership(freeT)(struct T* t) = T(t);

struct T* mkT(int x)
	//@ requires x >= 0;
	//@ ensures Ownership(freeT)(result);
{
	struct T* r = malloc(sizeof(struct T));
	if (r == 0) abort();
	r->value = x;
	//@ close Ownership(freeT)(r);
	return r;
}

void freeT(void* d) //@ : destructor
	//@ requires Ownership(freeT)(d);
	//@ ensures true;
{
	//@ open Ownership(freeT)(d);
	struct T* t = (struct T*)d;
	//@ open T(t);
	free(t);
}

void test_list()
	//@ requires true;
	//@ ensures  true;
{
	struct node *l = 0;
	//@ close list(l, freeT);
	l = cons(mkT(3), l);
	l = cons(mkT(4), l);
	if (!l) abort(); // we don't track size of list but head/tail require non-empty list
	struct T* x = head(&l);
	if (!l) abort(); // we don't track size of list but head/tail require non-empty list
	struct T* y = head(&l);

	// we don't track contents of list but we know that T(_) must hold for all elements
	//@ open Ownership(freeT)(x);
	//@ open Ownership(freeT)(y);
	//@ open T(x);
	//@ open T(y);
	assert(x->value >= 0);
	assert(y->value >= 0);

	//@ close Ownership(freeT)(x);
	//@ close Ownership(freeT)(y);
	freeT(x);
	freeT(y);

	// we don't track the size of a list so we cannot show that the list is empty so
	// we still have to dispose of it.
	list_dispose(l, freeT);
}

/****************************************************************
 * End
 ****************************************************************/
