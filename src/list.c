/****************************************************************
 * Singly linked list
 *
 * Copyright Alastair Reid 2020
 * SPDX-Licence-Identifier: BSD-3-Clause
 ****************************************************************/

#include "stdlib.h"

struct node {
    struct node *next;
    int value;
};

/*@

// Basic predicate about a single node
//
// Hoping to use this to reduce repetition in other predicates.
predicate node(struct node *n; struct node *next, int value) =
    n->next |-> next
    &*& n->value |-> value
    &*& malloc_block_node(n)
;

// The most basic linked list predicate.
// It just says that we have a linked list in the heap from first to last.
// Often used with "last == 0".
predicate lseg0(struct node *first, struct node *last;) =
    first == last
    ? true
    : first->next |-> ?next
      &*& first->value |-> ?value
      &*& malloc_block_node(first)
      &*& lseg0(next, last)
;

// More advanced linked list predicate that tracks length of list.
//
// Repetition of shape of a single node is unfortunate but it removes the
// need to constantly open/close nodes
predicate lseg1(struct node *first, struct node *last, int count) =
    first == last
    ? count == 0
    : first->next |-> ?next
      &*& first->value |-> ?value
      &*& malloc_block_node(first)
      &*& lseg1(next, last, count-1)
;

@*/

struct node *cons(struct node *head, int value)
	//@ requires lseg0(head, 0);
	//@ ensures lseg0(result, 0);
{
	struct node *n = malloc(sizeof(struct node));
	if (n == 0) { abort(); }
	n->next = head;
	n->value = value;
	return n;
}

struct node* tail(struct node *head)
	//@ requires lseg0(head, 0) &*& head != 0;
	//@ ensures  lseg0(result, 0);
{
	struct node* r = head->next;
	free(head);
	return r;
}

void list_dispose(struct node *first)
	//@ requires lseg0(first, 0);
	//@ ensures true;
{
	struct node *n = first;
	while (n != 0)
		//@ requires lseg0(n, 0);
		//@ ensures  true;
	{
		struct node *next = n->next;
		free(n);
		n = next;
	}
}

/****************************************************************
 * End
 ****************************************************************/
