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

/*@
predicate list(struct intrusive_list *l;) =
	l == 0
	? true
	: l->next |-> ?n
	&*& list(n)
;

predicate singleton(struct intrusive_list *l;) =
	l != 0
	&*& l->next |-> ?n
	&*& n == 0
;

lemma void singletons_are_lists_too(struct intrusive_list *l)
	requires singleton(l);
	ensures list(l);
{
	open singleton(l);
	close list(l);
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
	//@ requires singleton(x) &*& list(y);
	//@ ensures  list(x);
{
	x->next = y;
}

struct intrusive_list *tail(struct intrusive_list *l)
	//@ requires list(l) &*& l != 0;
	//@ ensures  list(l) &*& list(result);
{
	struct intrusive_list *r = l->next;
	l->next = 0;
	return r;
}

bool issingleton(struct intrusive_list *l)
	//@ requires list(l);
	//@ ensures  list(l);
{
	return l != 0 && l->next == NULL;
}

/****************************************************************
 * End
 ****************************************************************/
