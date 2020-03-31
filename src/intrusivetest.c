/****************************************************************
 * Singly linked intrusive list
 *
 * Copyright Alastair Reid 2020
 * SPDX-Licence-Identifier: BSD-3-Clause
 ****************************************************************/

#include "stdlib.h"
#include "intrusive.h"

struct list {
	int value;
	struct intrusive_list head;
};

// Test heap allocated lists
void test_list1()
	//@ requires true;
	//@ ensures  true;
{
	struct list* a = malloc(sizeof(struct list));
	struct list* b = malloc(sizeof(struct list));
	if (a == 0 || b == 0) abort();
	//@ assume(&a->head != 0 && &b->head != 0); // This assumption is safe but not ideal
	singleton(&a->head);
	singleton(&b->head);
	append(&a->head, &b->head);
	//@ open list(_, _);
	//@ open list(_, _);
	//@ open list(_, _);
	free(a);
	free(b);
	return;
}

// Test stack allocated list usage
void test_list2()
	//@ requires true;
	//@ ensures  true;
{
	struct list a;
	struct list b;
	//@ assume(&a.head != 0);   // These assumptions are not ideal
	//@ assume(&b.head != 0);
	singleton(&a.head);
	singleton(&b.head);
	append(&a.head, &b.head);
	//@ open list(_, _);
	//@ open list(_, _);
	//@ open list(_, _);
	return;
}

/*@
predicate is_head_field(struct intrusive_list *h, predicate(struct list *l) p);

lemma struct intrusive_list* head_of_list(struct list *l, predicate(struct list* l) p);
	requires p(l);
	ensures  *result |-> _ &*& is_head_field(result, p);

lemma struct list* list_of_head(struct intrusive_list *head, predicate(struct list* l) p);
	requires *head |-> _ &*& is_head_field(head, p);
	ensures  p(result);

@*/


#if 0 // hopelessly broken around the use of containerof
// Test list traversal
void test_list3()
	//@ requires true;
	//@ ensures  true;
{
	struct list a;
	struct list b;
	//@ assume(&a.head != 0);   // These assumptions are not ideal
	//@ assume(&b.head != 0);
	singleton(&a.head);
	singleton(&b.head);
	append(&a.head, &b.head);

	// struct list *pb = container_of(next(&a.head), struct list, head);
	size_t o = offsetof(struct list, head);
	size_t s = sizeof(struct list);
	struct intrusive_list* p = &(a.head);
	char q[ = (char*)p;
	// struct list *pb = next(&a.head), struct list, head);
	//@ open list(_, _);
	//@ open list(_, _);
	//@ open list(_, _);
	return;
}
#endif

#if 0

	l = cons(3, l);
	l = cons(4, l);
	if (!l) abort(); // we don't track size of list but head/tail require non-empty list
	int x = head(l);
	l = tail(l);
	if (!l) abort(); // we don't track size of list but head/tail require non-empty list
	int y = head(l);
	l = tail(l);
	// we don't track contents of list so we can't assert anything about x and y

	// we don't track the size of a list so we cannot show that the list does not leak
	// without disposing of it
	list_dispose(l);
}
#endif

/****************************************************************
 * End
 ****************************************************************/
