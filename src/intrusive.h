/****************************************************************
 * Singly linked, acyclic intrusive list
 *
 * Copyright Alastair Reid 2020
 * SPDX-Licence-Identifier: BSD-3-Clause
 ****************************************************************/

#include <stdbool.h>
#include <stddef.h>

// Note: intrusive lists are often used in operating system code
// where they are typically doubly linked and cyclic.
// These lists are neither because I want to tackle each of those
// challenges separately.
struct intrusive_list {
	struct intrusive_list *next;
};

// In ordinary linked list predicates, it is sufficient just to
// say that the list is correctly structured: it is not necessary
// for the predicate to talk about the contents of the list.
//
// But, when reasoning about intrusive lists, the struct is usually
// part of a struct that encloses it. So it is necessary to keep track
// of what nodes are in the list so that they can be recombined with
// the enclosing struct when elements are removed from the list.
/*@
predicate list(struct intrusive_list *l; list<struct intrusive_list *> cs) =
	l == 0
	? cs == nil
	: l->next |-> ?n
	&*& list(n, ?cs2)
	&*& cs == cons(l, cs2)
;

predicate singleton(struct intrusive_list *l;) =
	l != 0
	&*& l->next |-> ?n
	&*& n == 0
;

lemma void singletons_are_lists_too(struct intrusive_list *l)
	requires singleton(l);
	ensures list(l, cons(l, nil));
{
	open singleton(l);
	close list(l, _);
}
@*/

#define container_of(ptr, type, member) ((type *)((char *)ptr - offsetof(type, member)))

void singleton(struct intrusive_list *l)
	//@ requires l != 0 &*& l->next |-> _;
	//@ ensures  singleton(l);
{
	l->next = NULL;
}

void append(struct intrusive_list *x, struct intrusive_list *y)
	//@ requires singleton(x) &*& list(y, ?cs);
	//@ ensures  list(x, cons(x, cs));
{
	x->next = y;
}

struct intrusive_list *tail(struct intrusive_list *l)
	//@ requires list(l, cons(l, ?cs));
	//@ ensures  list(l, cons(l, nil)) &*& list(result, cs);
{
	//@ open list(l, _);
	struct intrusive_list *r = l->next;
	l->next = 0;
	return r;
}

bool issingleton(struct intrusive_list *l)
	//@ requires list(l, ?cs);
	//@ ensures  list(l, cs);
{
	return l != 0 && l->next == NULL;
}

/****************************************************************
 * End
 ****************************************************************/
