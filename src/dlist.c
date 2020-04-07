/****************************************************************
 * Doubly linked circular list
 *
 * Copyright Alastair Reid 2020
 * SPDX-Licence-Identifier: BSD-3-Clause
 ****************************************************************/

#include "stdlib.h"
#include "dlist.h"

struct node *insert_after(int x, struct node *xs)
	//@ requires dlist(xs);
	//@ ensures dlist(result);
{
	struct node *n = malloc(sizeof(struct node));
	if (n == 0) { abort(); }
	n->data = x;
	if (xs) {
		n->next = xs->next;
		xs->next = n;
	} else {
		n->next = 0;
	}
	n->prev = xs;
	return n;
}

struct node *insert_before(int x, struct node *xs)
	//@ requires dlist(xs);
	//@ ensures dlist(result);
{
	struct node *n = malloc(sizeof(struct node));
	if (n == 0) { abort(); }
	n->data = x;
	n->next = xs;
	n->prev = xs ? xs->prev : 0;
	return n;
}

int head(struct node *l)
	//@ requires dlist(l) &*& l != 0;
	//@ ensures  dlist(l);
{
	return l->data;
}

struct node* remove(struct node *l)
	//@ requires dlist(l) &*& l != 0;
	//@ ensures  dlist(result);
{
	struct node* n = l->next;
	struct node* p = l->prev;
	free(l);
	if (n) n->prev = p;
	if (p) p->next = n;
	return n ? n : p;
}

// combined head/tail function
int pop(struct node **pl)
	//@ requires *pl |-> ?l &*& dlist(l) &*& l != 0;
	//@ ensures  *pl |-> ?r &*& dlist(r);
{
	int data = (*pl)->data;
	struct node* n = (*pl)->next;
	struct node* p = (*pl)->prev;
	free(*pl);
	if (n) n->prev = p;
	if (p) p->next = n;
	*pl = n ? n : p;
	return data;
}

void dlist_dispose(struct node *l)
	//@ requires dlist(l);
	//@ ensures true;
{
	struct node *n = l;
	while (n != 0)
		//@ requires dlist(n);
		//@ ensures  true;
	{
		struct node *next = n->next;
		free(n);
		n = next;
	}
}

// This function is the same as dlist_dispose
// except that it uses a loop invariant
// instead of a loop specification.
void dlist_dispose2(struct node *l)
	//@ requires dlist(l);
	//@ ensures true;
{
	struct node *n = l;
	while (n != 0)
		//@ invariant dlist(n);
	{
		struct node *next = n->next;
		free(n);
		n = next;
	}
}

/****************************************************************
 * End
 ****************************************************************/
