/****************************************************************
 * Singly linked generic list
 *
 * Copyright Alastair Reid 2020
 * SPDX-Licence-Identifier: BSD-3-Clause
 ****************************************************************/

#include "list_generic.h"
#include "stdlib.h"

struct node *cons(void* x, struct node *xs)
	//@ requires list(xs, ?d) &*& Ownership(d)(x);
	//@ ensures  list(result, d);
{
	struct node *n = malloc(sizeof(struct node));
	if (n == 0) { abort(); }
	n->data = x;
	n->next = xs;
	//@ open list(xs, d);
	//@ close list(xs, d);
	//@ close list(n, d);
	return n;
}

void* pop(struct node **pl)
	//@ requires *pl |-> ?l &*& list(l, ?d) &*& l != 0;
	//@ ensures  *pl |-> ?r &*& list(r, d) &*& Ownership(d)(result);
{
	//@ open list(*pl, d);
	void *data = (*pl)->data;
	struct node* r = (*pl)->next;
	free(*pl);
	*pl = r;
	return data;
}

void list_dispose(struct node *l, destructor *f)
	//@ requires list(l, f);
	//@ ensures true;
{
	struct node *n = l;
	while (n != 0)
		//@ requires list(n, f);
		//@ ensures  list(n, f);
	{
		//@ open list(n, f);
		f(n->data);
		struct node *next = n->next;
		free(n);
		n = next;
	}
	//@ open list(n, f);
}

// This function is the same as list_dispose
// except that it uses a loop invariant
// instead of a loop specification.
void list_dispose2(struct node *l, destructor *f)
	//@ requires list(l, f);
	//@ ensures true;
{
	struct node *n = l;
	while (n != 0)
		//@ invariant list(n, f);
	{
		//@ open list(n, f);
		f(n->data);
		struct node *next = n->next;
		free(n);
		n = next;
	}
	//@ open list(n, f);
}

/****************************************************************
 * End
 ****************************************************************/
