/****************************************************************
 * A slightly better memory allocator
 *
 * This supports freeing memory.
 * The freelist is maintained in the freed objects themselves!
 *
 * Copyright Alastair Reid 2020
 * SPDX-Licence-Identifier: BSD-3-Clause
 ****************************************************************/

#include "stddef.h"
#include "stdint.h"

struct slab;

#if 1
// Unfortunately, VeriFast does not treat 'sizeof(T)' as a compile-time
// constant that it can use when reasoning so we have to expose this
// internal implementation detail so that we can talk about the size of
// it in pre/post-conditions.
struct freelist {
	struct freelist *next;
};

#define MIN_OBJ_SIZE sizeof(struct freelist)

#else

// The allocator has a certain minimum size of object that it
// can support.
#define MIN_OBJ_SIZE 64

#endif

/*@

// was this object allocated from a given slab allocator?
predicate slab_alloc_block(struct slab* s, void* p);

predicate slab_raw(struct slab *s;);

predicate slab(struct slab *s; size_t next, size_t chunksize, char* chunk, size_t size);
@*/

void slab_init(struct slab *s, char *p, size_t chunksize, size_t objsize);
	/*@ requires
		slab_raw(s)
		&*& p != 0
		&*& chars(p, chunksize, _)
		&*& chunksize <= UINT64_MAX
		&*& objsize >= MIN_OBJ_SIZE
		&*& objsize <= UINT64_MAX
		;
	@*/
	//@ ensures slab(s,_,_,_,objsize);
	//@ terminates;

void* slab_alloc(struct slab *s);
	//@ requires slab(s,_,?chunksize,?chunk,?sz);
	/*@ ensures
		slab(s,?next,chunksize,chunk,sz)
		&*& (result == 0 ?
			true
		:
			(   chars(result, sz, _)
			&*& slab_alloc_block(s, result)))
		;
	@*/
	//@ terminates;

void slab_free(struct slab *s, void* x);
	//@ requires slab(s,_,_,_,?sz) &*& x != 0 &*& chars(x, sz, _) &*& slab_alloc_block(s, x);
	//@ ensures  slab(s,_,_,_,sz);
	//@ terminates;

/****************************************************************
 * End
 ****************************************************************/

