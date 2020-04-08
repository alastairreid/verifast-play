/****************************************************************
 * Doubly linked circular list
 *
 * Copyright Alastair Reid 2020
 * SPDX-Licence-Identifier: BSD-3-Clause
 ****************************************************************/

struct node {
    int data;
    struct node *next;
    struct node *prev;
};

// Circular list starting with node i, ending with node k
/*@
predicate dlist(struct node *i, struct node *k;) =
    (i == 0 && k == 0)
    ? true
    : malloc_block_node(i)
      &*& i->data |-> _
      &*& i->next |-> ?j
      &*& i->prev |-> k
      &*& dlist(j, i)
;
@*/

struct node *insert_after(int x, struct node *xs);
	//@ requires dlist(xs, ?p);
	//@ ensures  dlist(result, p);

struct node *insert_before(int x, struct node *xs);
	//@ requires dlist(?p, xs);
	//@ ensures  dlist(p, result);

int head(struct node *l);
	//@ requires dlist(l, ?p) &*& l != 0;
	//@ ensures  dlist(l, p);

struct node* remove(struct node *l);
	//@ requires dlist(l, ?p) &*& l != 0;
	//@ ensures  dlist(result, p);

// combined head/tail function
int pop(struct node **pl);
	//@ requires *pl |-> ?l &*& dlist(l, ?p) &*& l != 0;
	//@ ensures  *pl |-> ?r &*& dlist(r, p);

void list_dispose(struct node *l);
	//@ requires dlist(l, _);
	//@ ensures true;

/****************************************************************
 * End
 ****************************************************************/
