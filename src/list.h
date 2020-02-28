/****************************************************************
 * Singly linked list
 *
 * Copyright Alastair Reid 2020
 * SPDX-Licence-Identifier: BSD-3-Clause
 ****************************************************************/

struct node {
    int value;
    struct node *next;
};

/*@
predicate list(struct node *l;) =
    l == 0
    ? true
    : malloc_block_node(l)
      &*& l->value |-> _
      &*& l->next  |-> ?n
      &*& list(n)
;
@*/

struct node *cons(int x, struct node *xs);
	//@ requires list(xs);
	//@ ensures  list(result);

int head(struct node *l);
	//@ requires list(l) &*& l != 0;
	//@ ensures  list(l);

struct node* tail(struct node *l);
	//@ requires list(l) &*& l != 0;
	//@ ensures  list(result);

void list_dispose(struct node *l);
	//@ requires list(l);
	//@ ensures true;

/****************************************************************
 * End
 ****************************************************************/
