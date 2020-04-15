/****************************************************************
 * Doubly linked, acyclic lists
 *
 * Inspired by
 * https://github.com/verifast/verifast/blob/master/examples/doubly_linked_list.c
 *
 * Copyright Alastair Reid 2020
 * SPDX-Licence-Identifier: BSD-3-Clause
 ****************************************************************/

//@ #include "list.gh"
//@ #include "listex.gh"

struct node {
	int data;
	struct node *next;
	struct node *prev;
};

struct dllist {
	struct node *head;
	struct node *tail;
};

/*@
predicate node(struct node *t; int d, struct node *n, struct node *p) =
	malloc_block_node(t)
	&*& t->data |-> d
	&*& t->next |-> n
	&*& t->prev |-> p
;

// Nodes of a doubly linked list - following the next links
predicate list_next(struct node *l; list<struct node*> ls) =
	l == 0
	? ls == nil
	: node(l, _, ?n, _)
	&*& list_next(n, ls2)
	&*& ls == cons(l, ls2)
;

// Nodes of a doubly linked list - following the prev links
// The problem is that this describes ownership so I cannot use it
// in conjunction with list_next
predicate list_prev(struct node *l; list<struct node*> ls) =
	l == 0
	? ls == nil
	: node(l, _, _, ?p)
	&*& list_prev(n, ls2)
	&*& ls == cons(l, ls2)
;

// Links of a doubly linked list - resulting in two lists of nodes:
// - ns = [x1, ... xm]
// - ps = [0, x1, ... xm-1]
// where
//   x1 is the first node in the list (the tail)
//   x2, ... xm are reached by following the next links from x1
//   x1 == l
// (The null pointer at the head of ps is because that is l->prev)
//
// Note: minor variations on this design include:
// - (ns, ps) = ([x2, ... xm, 0], [0, x1, ... xm-1])
// - (ns, ps) = ([x1, ... xm, 0], [0, x1, ... xm])

predicate list2(struct node *l; list<struct node*> ns, list<struct node*> ps) =
	l == 0
	? ns == nil &*& ps == nil
	: node(l, _, ?n, ?p)
	&*& list2(n, ns2, ps2)
	&*& ns == cons(l, ns2) // choice of n or l?
	&*& ps == cons(p, ps2)
;

// Variant of list2 that checks that prev links are correct
// ls = [x1, ... xm]
// where
//   x1->prev == a
//   x1 == b
predicate list3(struct node *a; struct node *b; list<struct node*> ls) =
	b == 0
	? a == 0 &*& ls == nil
	: node(b, _, ?c, ?p)
	&*& p == a
	&*& list3(b, c, ls2)
	&*& ls == cons(b, ls2)
;

// Variant of list3 that traverses list in opposite order
// (following prev links and checking next links)
// ls = [x1, ... xm]
// where
//   x1->next == b
//   x1 == a
predicate list4(struct node *a; struct node *b; list<struct node*> ls) =
	b == 0
	? a == 0 &*& ls == nil
	: node(b, _, ?n, ?c)
	&*& p == a
	&*& list3(b, c, ls2)
	&*& ls == cons(b, ls2)
;

// Variant of list4 that omits the list argument
predicate list5(struct node *a; struct node *b) =
	b == 0
	? a == 0 &*& ls == nil
	: node(b, _, ?c, ?p)
	&*& p == a
	&*& list3(b, c)
;

// First attempt at specifying shape of dlllist
// Problem: does not check that 'h' is last node
predicate dl(struct dllist *d)
	=   d->head |-> ?h
	&*& d->tail |-> ?t
	&*& (h == 0) == (t == 0)
	&*& ( t == 0
	    ? h == 0
	    : t->prev |-> ?p
	      &*& list5(t, p)
	    )
;




// ns and ps are lists of equal length that are either empty (if h is nil) or
// - ns = [h, x1, ... xm, 0]
// - ps = [p, h, x1, ... xm]
// where p is the h->prev
//   and [x1, ... xm] are h->next, h->next->next, ... ]
predicate list(struct node *h; nlist ns, nlist ps) =
	h == 0
	? ps == nnil &*& ns == nnil
	: node(h, _, ?n, ?p)
	&*& list(n, ?ns2, ?ps2)
	&*& ns == ncons(h, ns2)
	&*& ps == ncons(p, ps2)
;


#if 0
todo:
- switch to using list library (verifast/bin/list.gh and listex.gh)
Contents:
- inductive list
- fixpoints head, tail, length, append, reverse, mem, nth, distinct, take, drop, remove, index_of
- predicate foreach
- fixpoints map, forall, exists, update
- Some of the more relevant seeming lemmas

	lemma_auto void append_nil<t>(list<t> xs);
	lemma void append_assoc<t>(list<t> xs, list<t> ys, list<t> zs);
	lemma void reverse_append<t>(list<t> xs, list<t> ys);
	lemma_auto void reverse_reverse<t>(list<t> xs);
	lemma void foreach_append<t>(list<t> xs, list<t> ys);
	lemma void forall_append<t>(list<t> xs, list<t> ys, fixpoint(t, bool) p);



- define snoc function
- define:
	- nodes_next = all nodes read along next links from tail [n1, ... nm]
	- nodes_prev = all nodes read along prev links from head [nm, ... n1]
	- don't try to combine the two definitions (as in the double-list.c code) unless forced to combine them.
	- but, beware that the ownership part has to pick a direction - so maybe one of them does have to be combined?
- prove that insert head/tail performs:
	- cons on nodes_next and snoc on nodes_prev
	or
	- snoc on nodes_next and cons on nodes_prev
	use these proofs in the insert-head/tail functions
- define tail and liat functions
	- prove that remove head/tail performs:
		- tail on one list, liat on the other
	use these proofs in the remove-head/tail functions
- possibly prove that all operations preserve: nodes_next(l) == rev(nodes_prev(l))
#endif

inductive nlist =
	| nnil
	| ncons(struct node*, nlist)
;


// ns and ps are two lists of nodes of equal length that are either empty or
// - ns = [x1, ... xm, t]
// - ps = [h, x1, ..., xm]
predicate linked(struct node *t, nlist ns, nlist ps, struct node *h) =
	ns == nnil
	? t == h &*& ps == nnil
	: linked(t, ?ns2, ?ps2, ?h2)
	&*& ns == ncons(h2, ns2)
	&*& ps == ncons(h, ps2)
;

// ns and ps are lists of equal length that are either empty (if h is nil) or
// - ns = [h, x1, ... xm, 0]
// - ps = [p, h, x1, ... xm]
// where p is the h->prev
//   and [x1, ... xm] are h->next, h->next->next, ... ]
predicate list(struct node *h; nlist ns, nlist ps) =
	h == 0
	? ps == nnil &*& ns == nnil
	: node(h, _, ?n, ?p)
	&*& list(n, ?ns2, ?ps2)
	&*& ns == ncons(h, ns2)
	&*& ps == ncons(p, ns2)
;

// Doubly linked, possibly empty list, acyclic list
// If not empty,
// - ns is the list of nodes from following the tail/next pointers
// - ps is the list of predecessors of those nodes
// Following next pointers from tail leads to head.
// Following prev pointers from head leads to tail.
predicate dll(struct dllist *d)
	=   d->head |-> ?h
	&*& d->tail |-> ?t
	&*& (h == 0) == (t == 0)
	&*& list(h, ?ns, ?ps)
	&*& linked(t, ns, ps, 0)
;

@*/

void init(struct dllist *l);
	//@ requires l->head |-> _ &*& l->tail |-> _;
	//@ ensures  dll(l);

void insert_at_head(int x, struct dllist *l);
	//@ requires dll(l);
	//@ ensures  dll(l);

void insert_at_tail(int x, struct dllist *l);
	//@ requires dll(l);
	//@ ensures  dll(l);

int pop(struct dllist *l);
	//@ requires dll(l) &*& l != 0;
	//@ ensures  dll(l);

void list_dispose(struct dllist *l);
	//@ requires dll(l);
	//@ ensures true;

#if 0

/*@
// Doubly linked acyclic list segment with two sets of links:
// - Forward list from n1 to n2 through the "next" fields
// - Backward list from p2 to p1 through the "prev" fields
// (To turn this into a cyclic list, the ends are joined
// together by inserting a "root" node.)
predicate dlist1(struct node *n1, struct node *p1, struct node *n2, struct node *p2) =
    (n1 == n2 && p1 == p2)
    ? true
    : malloc_block_node(n1)
      &*& n1->data |-> _
      &*& n1->next |-> ?n3
      &*& n1->prev |-> p1
      &*& dlist1(n3, n1, n2, p2)
;

// Alternate predicate for doubly linked lists that recurses
// along "prev" links
predicate dlist2(struct node *n1, struct node *p1, struct node *n2, struct node *p2) =
    (n1 == n2 && p1 == p2)
    ? true
    : malloc_block_node(p2)
      &*& p2->data |-> _
      &*& p2->next |-> n2
      &*& p2->prev |-> ?p3
      &*& dlist2(n1, p1, p2, p3)
;

lemma void singleton1(struct node *p, struct node *i, struct node *n)
	requires malloc_block_node(i) &*& i->data |-> _ &*& i->next |-> n &*& i->prev |-> p &*& i != n &*& i != p;
	ensures dlist1(i,p,n,i);
{
	close dlist1(n,i,n,i);
	close dlist1(i,p,n,i);
}

lemma void snoc(
	struct node *n1,
	struct node *p1,
	struct node *n2,
	struct node *p2,
	struct node *n3)
	requires dlist1(n1,p1,n2,p2) &*& malloc_block_node(n2) &*& n2->data |-> _ &*& n2->next |-> n3 &*& n2->prev |-> p2 &*& n1 != n3 &*& p1 != n2;
	ensures dlist1(n1,p1,n3,n2);
{
	if (n1 == n2 && p1 == p2) {
		open dlist1(n1,p1,n2,p2);
		singleton1(p1,n2,n3);
	} else {
		open dlist1(n1,p1,n2,p2);
		snoc(n1->next,n1,n2,p2,n3);
	}
}

#if 0
lemma void dlist_to_dlist2(
	struct node *n1,
	struct node *p1,
	struct node *n2,
	struct node *p2)
	requires dlist1(n1,p1,n2,p2);
	ensures  dlist2(n1,p1,n2,p2);
{
}
#endif

#if 0
// changing view of a doubly-linked acyclic list
lemma void dlist_to_dlist2(struct node *i)
	requires malloc_block_node(i) &*& i->data |-> _ &*& i->next |-> ?n &*& i->prev |-> ?p &*& dlist(n,i,i,p);
	ensures  malloc_block_node(i) &*& i->data |-> _ &*& i->next |-> n &*& i->prev |-> p &*& dlist2(n,i,i,p);
{
	open dlist(n,i,i,p);
	if (i == n && i == p) {
	} else {
		close dlist(n,i,n,i);
		close dlist(i,p,n,i);
		join_dlist(n->next,n,i,p,n,i);
		dlist_to_dlist2(n);
	}
	close dlist2(n,i,i,p);
}
#endif

// Circular, doubly-linked list
predicate clist(struct node *i) =
    i == 0
    ? true
    : malloc_block_node(i)
      &*& i->data |-> _
      &*& i->next |-> ?n
      &*& i->prev |-> ?p
      &*& dlist1(n, i, i, p)
;
@*/

/****************************************************************
 * End
 ****************************************************************/
