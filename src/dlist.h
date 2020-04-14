/****************************************************************
 * Non-empty, doubly linked circular
 *
 * Copyright Alastair Reid 2020
 * SPDX-Licence-Identifier: BSD-3-Clause
 ****************************************************************/

struct node {
    int data;
    struct node *next;
    struct node *prev;
};

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

struct node *insert_after(int x, struct node *xs);
	//@ requires clist(xs);
	//@ ensures  clist(result);

struct node *insert_before(int x, struct node *xs);
	//@ requires clist(xs);
	//@ ensures  clist(result);

int head(struct node *l);
	//@ requires clist(l) &*& l != 0;
	//@ ensures  clist(l);

struct node* remove(struct node *l);
	//@ requires clist(l) &*& l != 0;
	//@ ensures  clist(result);

// combined head/tail function
int pop(struct node **pl);
	//@ requires *pl |-> ?l &*& clist(l) &*& l != 0;
	//@ ensures  *pl |-> ?r &*& clist(r);

void list_dispose(struct node *l);
	//@ requires clist(l);
	//@ ensures true;

/****************************************************************
 * End
 ****************************************************************/
