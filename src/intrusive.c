/****************************************************************
 * Singly linked intrusive list
 *
 * Copyright Alastair Reid 2020
 * SPDX-Licence-Identifier: BSD-3-Clause
 ****************************************************************/

#include "intrusive.h"

struct node {
    int value;
    struct intrusive_list list;
};

/*@
predicate list(struct node *l;) =
    l == 0
    ? true
    : malloc_block_node(l)
      &*& l->value |-> _
      &*& l->next  |-> ?n
      &*& list(n)
;
@*/

struct node *cons(int x, struct node *xs);
	//@ requires list(xs);
	//@ ensures  list(result);

int head(struct node *l);
	//@ requires list(l) &*& l != 0;
	//@ ensures  list(l);

struct node* tail(struct node *l);
	//@ requires list(l) &*& l != 0;
	//@ ensures  list(result);

void list_dispose(struct node *l);
	//@ requires list(l);
	//@ ensures true;

/****************************************************************
 * End
 ****************************************************************/
struct list {

struct node *cons(int x, struct node *xs)
	//@ requires list(xs);
	//@ ensures list(result);
{
	struct node *n = malloc(sizeof(struct node));
	if (n == 0) { abort(); }
	n->value = x;
	n->next = xs;
	return n;
}

int head(struct node *l)
	//@ requires list(l) &*& l != 0;
	//@ ensures  list(l);
{
	return l->value;
}

struct node* tail(struct node *l)
	//@ requires list(l) &*& l != 0;
	//@ ensures  list(result);
{
	struct node* r = l->next;
	free(l);
	return r;
}

void list_dispose(struct node *l)
	//@ requires list(l);
	//@ ensures true;
{
	struct node *n = l;
	while (n != 0)
		//@ requires list(n);
		//@ ensures  true;
	{
		struct node *next = n->next;
		free(n);
		n = next;
	}
}

// This function is the same as list_dispose
// except that it uses a loop invariant
// instead of a loop specification.
void list_dispose2(struct node *l)
	//@ requires list(l);
	//@ ensures true;
{
	struct node *n = l;
	while (n != 0)
		//@ invariant list(n);
	{
		struct node *next = n->next;
		free(n);
		n = next;
	}
}

/****************************************************************
 * End
 ****************************************************************/
