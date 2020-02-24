/****************************************************************
 * A slab allocator
 *
 * Copyright Alastair Reid 2020
 * SPDX-Licence-Identifier: BSD-3-Clause
 ****************************************************************/

#include "stddef.h"
#include "stdint.h"
#include "stdlib.h"
#include "wrap.h"

#define HEAP_SIZE 10000

struct slab {
	size_t next;
	char *heap;
};

/*@
predicate slab_raw(struct slab *s;) =
	s->next |-> _ &*& s->heap |-> _
;

predicate slab(struct slab *s; size_t next, char* heap) =
    s->next |-> next
    &*& s->heap |-> heap
    &*& heap > 0
    &*& 0 <= next &*& next < HEAP_SIZE
    &*& chars(heap+next, HEAP_SIZE - next, _)
;
@*/

void slab_init(struct slab *s, char *p)
	/*@ requires
		slab_raw(s)
		&*& p != 0
		&*& chars(p, HEAP_SIZE, _)
		;
	@*/
	//@ ensures slab(s,_,_);
	//@ terminates;
{
	s->next = 0;
	s->heap = p;
}

char* slab_alloc(struct slab *s, size_t size)
	//@ requires slab(s,_,_) &*& size < UINT32_MAX;
	/*@ ensures
		slab(s,?next,?heap)
		&*& (result == 0 ?
			true
		:
			chars(result, size, _)
			&*& heap <= result
			&*& result + size < heap + HEAP_SIZE)
		;
	@*/
	//@ terminates;
{
	if (wrap_add64(s->next, size) >= HEAP_SIZE) {
		return 0;
	} else {
		//@ chars_split(s->heap + s->next, size);
		char *r = (char*)wrap_add64((uint64_t)s->heap, s->next);
		s->next = s->next + size;
		return r;
	}
}

/****************************************************************
 * Sequential tests
 ****************************************************************/

struct slab myslab;
char heap[HEAP_SIZE];

// Sequential test code
void test_slab_sequential()
	//@ requires slab_raw(&myslab) &*& chars(heap, HEAP_SIZE, _);
	//@ ensures  true;
	//@ terminates;
{
	//@ assume (&heap != 0);
	slab_init(&myslab, heap);
	char *t = slab_alloc(&myslab, 100);
	if (t == 0) abort();
	//@ leak chars(t, 100, _);
	//@ leak slab(&myslab, _, _);
}

/****************************************************************
 * End
 ****************************************************************/
