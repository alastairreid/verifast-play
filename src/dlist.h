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
// Doubly linked list segment with two sets of links:
// - Forward list from n1 to n2 through the "next" fields
// - Backward list from p2 to p1 through the "prev" fields
predicate dlist(struct node *n1, struct node *p1, struct node *n2, struct node *p2) =
    (n1 == n2 && p1 == p2)
    ? true
    : malloc_block_node(n1)
      &*& n1->data |-> _
      &*& n1->next |-> ?n3
      &*& n1->prev |-> p1
      &*& dlist(n3, n1, n2, p2)
;

lemma void join_dlist(
	struct node *n1, struct node *p1,
	struct node *n2, struct node *p2,
	struct node *n3, struct node *p3);
	requires dlist(n1,p1,n2,p2) &*& dlist(n2,p2,n3,p3);
	ensures dlist(n1,p1,n3,p3);

// This can't hold for arbitrary n2/p2 - what is an appropriate restriction?
lemma void split_dlist(
	struct node *n1, struct node *p1,
	struct node *n2, struct node *p2,
	struct node *n3, struct node *p3);
	requires dlist(n1,p1,n3,p3);
	ensures dlist(n1,p1,n2,p2) &*& dlist(n2,p2,n3,p3);

// Circular, doubly-linked list
predicate clist(struct node *i) =
    i == 0
    ? true
    : malloc_block_node(i)
      &*& i->data |-> _
      &*& i->next |-> ?n
      &*& i->prev |-> ?p
      &*& dlist(n, i, i, p);
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
