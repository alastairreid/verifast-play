/****************************************************************
 * Test for memory allocator
 *
 * Copyright Alastair Reid 2020
 * SPDX-Licence-Identifier: BSD-3-Clause
 ****************************************************************/

#include "stddef.h"
#include "stdint.h"
#include "stdlib.h"

#include "malloc1.h"

/****************************************************************
 * Sequential tests
 ****************************************************************/

struct slab myslab;

#define HEAP_SIZE 10000

char heap[HEAP_SIZE];

// Sequential test code
void test_slab_sequential()
	//@ requires slab_raw(&myslab) &*& chars(heap, HEAP_SIZE, _);
	//@ ensures  true;
	//@ terminates;
{
	size_t objsize = 256; // size of objects
	//@ assume (&heap != 0);
	//@ assume (sizeof(struct freelist) <= objsize);
	slab_init(&myslab, heap, HEAP_SIZE, objsize);
	void *t1 = slab_alloc(&myslab);
	if (t1 == 0) abort();
	void *t2 = slab_alloc(&myslab);
	if (t2 == 0) abort();
	slab_free(&myslab, t1);
	slab_free(&myslab, t2);
	//@ leak slab(&myslab, _, _, _, _);
}

/****************************************************************
 * End
 ****************************************************************/