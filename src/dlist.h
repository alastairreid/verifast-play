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

/*@
predicate dlist(struct node *l;) =
    l == 0
    ? true
    : malloc_block_node(l)
      &*& l->data |-> _
      &*& l->next |-> ?n
      &*& l->prev |-> ?p
      &*& dlist(n)
;
@*/

struct node *insert_after(int x, struct node *xs);
	//@ requires dlist(xs);
	//@ ensures  dlist(result);

struct node *insert_before(int x, struct node *xs);
	//@ requires dlist(xs);
	//@ ensures  dlist(result);

int head(struct node *l);
	//@ requires dlist(l) &*& l != 0;
	//@ ensures  dlist(l);

struct node* remove(struct node *l);
	//@ requires dlist(l) &*& l != 0;
	//@ ensures  dlist(result);

// combined head/tail function
int pop(struct node **pl);
	//@ requires *pl |-> ?l &*& dlist(l) &*& l != 0;
	//@ ensures  *pl |-> ?r &*& dlist(r);

void list_dispose(struct node *l);
	//@ requires dlist(l);
	//@ ensures true;

/****************************************************************
 * End
 ****************************************************************/
