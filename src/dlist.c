/****************************************************************
 * Doubly linked acyclic list
 *
 * Copyright Alastair Reid 2020
 * SPDX-Licence-Identifier: BSD-3-Clause
 ****************************************************************/

#include "stdlib.h"
#include "dlist.h"

void init(struct dllist *l)
	//@ requires l->head |-> _ &*& l->tail |-> _;
	//@ ensures  dll(l);
{
	l->head = 0;
	l->tail = 0;
	//@ close linked(0, nnil, nnil, 0);
	//@ close dll(l);
}

#if 0
void insert_at_head(int x, struct dllist *l)
	//@ requires dll(l);
	//@ ensures  dll(l);
{
	//@ open dll(l);
	// the following assertion is just to get the values of ns and ps
	//@ assert l->head |-> ?h &*& l->tail |-> ?t &*& list(h,?ns,?ps) &*& linked(t, ns, ps, 0);
	struct node *i = malloc(sizeof(struct node));
	if (i == 0) { abort(); }
	i->data = x;
	i->next = 0;
	i->prev = l->head;
	if (l->tail == 0) {
		//@ open  list(h, ns, ps); // open and close list(h,_,_);
		//@ close list(h, ns, ps);
		//@ assert ns == nnil && ps == nnil;
		//@ assert h == 0;
		//@ open linked(t, ns, ps, 0);
		//@ close list(i, ncons(i,nnil), ncons(0,nnil));
		//@ close linked(i, nnil, nnil, i);
		//@ close linked(i, ncons(i,nnil), ncons(0,nnil), 0);
		l->tail = i;
	} else {
		//@ open  list(h, ns, ps); // open and close list(h,_,_);
		//@ close list(h, ns, ps);
		//@ open  linked(t,ns,ps,0);
		//@ close linked(t,ns,ps,0);
		//
		//snoc lines are going to require induction to prove
		//@ assert ns == snoc(?ns2,0);
		//@ close linked(t, snoc(snoc(ns2,i),0), snoc(ps,i), 0);
		l->head->next = i;
		//@ close list(h, ncons(h,ns), ncons(0,ncons(h,ps2)));
	}
	l->head = i;
	//@ close dll(l);
}
#endif

#if 1
void insert_at_tail(int x, struct dllist *l)
	//@ requires dll(l);
	//@ ensures  dll(l);
{
	//@ open dll(l);
	// the following assertion is just to get the values of ns and ps
	//@ assert l->head |-> ?h &*& l->tail |-> ?t &*& list(h,?ns,?ps) &*& linked(t, ns, ps, 0);
	struct node *i = malloc(sizeof(struct node));
	if (i == 0) { abort(); }
	i->data = x;
	i->next = l->tail;
	i->prev = 0;
	if (l->head == 0) {
		l->head = i;
		//@ open list(h, ns, ps);
		//@ open linked(t, ns, ps, 0);
		//@ assert ns == nnil;
		//@ assert ps == nnil;
		//@ close linked(i, nnil, nnil, i);
		//@ close linked(i, ncons(i,nnil), ncons(0,nnil), 0);
	} else {
		//@ open list(h, ns, ps);
		//@ assert ps == ncons(_,?ps2);
		//
		//next line is going to require induction to prove
		//@ close linked(i, ncons(i,ns), ncons(0,ps), 0);
		//@ close list(h, ncons(i,ns), ncons(0,ncons(i,ps2)));
	}
	l->tail = i;
	//@ close dll(l);
}
#endif

#if 0
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
#endif

/****************************************************************
 * End
 ****************************************************************/
