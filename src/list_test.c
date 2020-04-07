/****************************************************************
 * Singly linked list
 *
 * Copyright Alastair Reid 2020
 * SPDX-Licence-Identifier: BSD-3-Clause
 ****************************************************************/

#include "stdlib.h"
#include "list.h"

void test_list()
	//@ requires true;
	//@ ensures  true;
{
	struct node *l = 0;
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

/****************************************************************
 * End
 ****************************************************************/
