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
/****************************************************************
 * End
 ****************************************************************/
