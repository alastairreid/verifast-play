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

#if 0
// Test stack allocated list usage
// Does not currently work - hard to describe the leaks at the end
void test_list1()
	//@ requires true;
	//@ ensures  true;
{
	struct list a;
	struct list b;
	//@ assume(&a.head != 0);   // These assumptions are not ideal
	//@ assume(&b.head != 0);
	singleton(&a.head);
	singleton(&b.head);
	//@ singletons_are_lists_too(&b.head);
	append(&a.head, &b.head);
	return;
}
#endif

// Test heap allocated lists
void test_list2()
	//@ requires true;
	//@ ensures  true;
{
	struct list* a = malloc(sizeof(struct list));
	struct list* b = malloc(sizeof(struct list));
	if (a == 0 || b == 0) abort();
	//@ assume(&a->head != 0 && &b->head != 0); // This assumption is safe but not ideal
	singleton(&a->head);
	singleton(&b->head);
	//@ singletons_are_lists_too(&b->head);
	append(&a->head, &b->head);
	//@ open list(_, _);
	//@ open list(_, _);
	//@ open list(_, _);
	free(a);
	free(b);
	return;
}

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
