/****************************************************************
 * Singly linked generic list
 *
 * Copyright Alastair Reid 2020
 * SPDX-Licence-Identifier: BSD-3-Clause
 ****************************************************************/

struct node {
    struct node *next;
    void* data;
};

//@ predicate_family Ownership(void *destructor)(void *data);

typedef void destructor(void* d);
	//@ requires Ownership(this)(d);
	//@ ensures true;

/*@
predicate list(struct node *l, destructor* destructor) =
    is_destructor(destructor) == true
    &*& (l == 0
        ? true
        : malloc_block_node(l)
          &*& l->data |-> ?d
          &*& Ownership(destructor)(d)
          &*& l->next |-> ?n
          &*& list(n, destructor))
;
@*/

struct node *cons(void* x, struct node *xs);
	//@ requires list(xs, ?d) &*& Ownership(d)(x);
	//@ ensures  list(result, d);

// return head of list and remove it from original list
void* head(struct node **pl);
	//@ requires *pl |-> ?l &*& list(l, ?d) &*& l != 0;
	//@ ensures  *pl |-> ?r &*& list(r, d) &*& Ownership(d)(result);

void list_dispose(struct node *l, destructor *f);
	//@ requires list(l, f);
	//@ ensures true;

/****************************************************************
 * End
 ****************************************************************/
