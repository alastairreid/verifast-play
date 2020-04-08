/****************************************************************
 * Doubly linked circular list
 *
 * Copyright Alastair Reid 2020
 * SPDX-Licence-Identifier: BSD-3-Clause
 ****************************************************************/

#include "stdlib.h"
#include "dlist.h"

struct node *insert_after(int x, struct node *xs)
	//@ requires clist(xs);
	//@ ensures clist(result);
{
	struct node *i = malloc(sizeof(struct node));
	if (i == 0) { abort(); }
	i->data = x;

	//@ open clist(xs);
	if (xs) {
		struct node *n = xs->next;
		//@ struct node *p = xs->prev;
		//@ open dlist(n,xs,xs,p);
		i->next = n;
		i->prev = xs;
		xs->next = i;
		n->prev = i;
		//@ close dlist(n,i,xs,xs->prev);
		//@ close dlist(i,xs,i,xs);
		//@ close dlist(xs,n==xs ? i : p,i,xs);
		//@ join_dlist(n,i,xs,n==xs ? i : p,i,xs);
	} else {
		i->next = i;
		i->prev = i;
		//@ close dlist(i,i,i,i);
	}
	return i;
	//@ close clist(i);
}

struct node *insert_before(int x, struct node *xs)
	//@ requires clist(xs);
	//@ ensures clist(result);
{
	struct node *i = malloc(sizeof(struct node));
	if (i == 0) { abort(); }
	i->data = x;
	if (xs) {
		//@ open clist(xs);
		//@ struct node *n = xs->next;
		struct node *p = xs->prev;
		xs->prev = i;
		//@ close dlist(xs,i,xs,p);
		p->next = i;
		//@ open dlist(n,xs,xs,p);
		i->next = xs;
		i->prev = p;
		//@ close dlist(i,n,i,n);
		//@ close dlist(n, n==xs?i:xs, i, n==xs?xs:p);
		//@ close clist(i);
	} else {
		i->next = i;
		i->prev = i;
		//@ close dlist(i,i,i,i);
		//@ close clist(i);
	}
	return i;
}

int head(struct node *l)
	//@ requires clist(l) &*& l != 0;
	//@ ensures  clist(l);
{
	return l->data;
}

struct node* remove(struct node *l)
	//@ requires clist(l) &*& l != 0;
	//@ ensures  clist(result);
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
	//@ requires *pl |-> ?l &*& clist(l) &*& l != 0;
	//@ ensures  *pl |-> ?r &*& clist(r);
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
	//@ requires clist(l);
	//@ ensures true;
{
	struct node *n = l;
	while (n != 0)
		//@ requires clist(n);
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
	//@ requires clist(l);
	//@ ensures true;
{
	struct node *n = l;
	while (n != 0)
		//@ invariant clist(n);
	{
		struct node *next = n->next;
		free(n);
		n = next;
	}
}

/****************************************************************
 * End
 ****************************************************************/
