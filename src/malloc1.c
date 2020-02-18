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
#include "wrap.h"

#include "malloc1.h"

#if 0
struct freelist {
	struct freelist *next;
};
#endif

/*@

// We state without proof...
// (Ideally, the SMT solver would just confirm this is true - but, for some
// reason, it does not.)
lemma void add_preserves_alignment(uint64_t x, uint64_t y, size_t alignment);
	requires
		is_aligned(x, alignment)
		&*& is_aligned(y, alignment)
		&*& alignment != 0
		&*& is_aligned((UINT64_MAX+1), alignment);
	ensures is_aligned(x + y, alignment);

@*/

/*@

// Freelist nodes padded out to some size 'sz'
// todo: doesn't actually require that they are padded
predicate freelist_node(struct freelist *l, size_t sz; struct freelist *n) =
    sz >= sizeof(struct freelist)
    &*& aligned(l, MIN_ALIGNMENT)
    &*& l->next |-> n
    &*& struct_freelist_padding(l)
    &*& chars((void*)l + sizeof(struct freelist), sz - sizeof(struct freelist), _)
;

// Acycyclic lists of freelist nodes all padded out to some size
predicate freelist(struct freelist *l, size_t sz;) =
    l == 0
    ? true
    : freelist_node(l, sz, ?next)
      &*& freelist(next, sz)
;

// This lemma can be used to convert a block of memory to a freelist
lemma void chars_to_freelist(void *x)
	requires chars(x, ?sz, _) &*& aligned(x, MIN_ALIGNMENT) &*& sz >= sizeof(struct freelist);
	ensures freelist_node((struct freelist*)x, sz, _);
{
	chars_split(x, sizeof(struct freelist));
	struct freelist* r = (struct freelist*)x;
	close_struct(r);
}

// This lemma can be used to convert a freelist entry to a block of characters
lemma void freelist_to_chars(struct freelist *x, size_t sz)
	requires freelist_node(x, sz, _) &*& sz >= sizeof(struct freelist);
	ensures chars((void*)x, sz, _) &*& aligned(x, MIN_ALIGNMENT);
{
	open_struct(x);
	chars_join((void*)x);
}

@*/

struct slab {
	size_t next;
	char  *chunk;
	size_t chunksize;
	size_t objsize; // size of objects
	struct freelist *free; // deallocated objects
};

/*@

// was this object allocated from a given slab allocator?
predicate slab_alloc_block(struct slab* s, void* p) = aligned(p, MIN_ALIGNMENT);
@*/


/*@
predicate slab_raw(struct slab *s;) =
	s->next |-> _
	&*& s->chunk |-> _
	&*& s->chunksize |-> _
	&*& s->objsize |-> _
	&*& s->free |-> _
;

predicate slab(struct slab *s; size_t next, size_t chunksize, char* chunk, size_t size) =
    s->next |-> next
    &*& s->chunk |-> chunk
    &*& s->chunksize |-> chunksize
    &*& s->objsize |-> size
    &*& s->free |-> ?free

    &*& freelist(free, size)
    &*& is_aligned(size, MIN_ALIGNMENT)
    &*& is_aligned(next, MIN_ALIGNMENT)
    &*& is_aligned(chunk, MIN_ALIGNMENT)
    &*& chunk > 0
    &*& MIN_OBJ_SIZE <= size &*& size < UINT64_MAX
    &*& 0 <= next &*& next <= chunksize
    &*& chunksize <= UINT64_MAX
    &*& chars(chunk+next, chunksize - next, _)
;
@*/

void slab_init(struct slab *s, char *p, size_t chunksize, size_t objsize)
	/*@ requires
		slab_raw(s)
		&*& p != 0
		&*& is_aligned(p, MIN_ALIGNMENT)
		&*& is_aligned((void*)objsize, MIN_ALIGNMENT)
		&*& chars(p, chunksize, _)
		&*& chunksize <= UINT64_MAX
		&*& MIN_OBJ_SIZE <= objsize &*& objsize <= UINT64_MAX
		;
	@*/
	//@ ensures slab(s,_,_,_,objsize);
	//@ terminates;
{
	s->next = 0;
	s->chunk = p;
	s->chunksize = chunksize;
	s->objsize = objsize;
	s->free = 0;
}

void* slab_alloc(struct slab *s)
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
{
	if (s->free) {
		struct freelist *f = s->free;
		s->free = f->next;
		//@ freelist_to_chars(f, sz);
		void* r = f;
		//@ close slab_alloc_block(s, r);
		return r;
	} else {
		size_t size = s->objsize;
		if (wrap_add64(s->next, size) >= chunksize) {
			return 0;
		} else {
			//@ chars_split(s->chunk + s->next, size);
			char *r = (char*)wrap_add64((uint64_t)s->chunk, s->next);
			// We have to encourage VeriFast to realize that addition preserves alignment
			//@ add_preserves_alignment((uint64_t)s->chunk, s->next, MIN_ALIGNMENT);
			//@ add_preserves_alignment(s->next, size, MIN_ALIGNMENT);
			s->next = s->next + size;
			//@ close slab_alloc_block(s, r);
			return r;
		}
	}
}

void slab_free(struct slab *s, void* x)
	//@ requires slab(s,_,_,_,?sz) &*& x != 0 &*& chars(x, sz, _) &*& slab_alloc_block(s, x);
	//@ ensures  slab(s,_,_,_,sz);
	//@ terminates;
{
	//@ open slab_alloc_block(s, x);
	//@ open slab(s,_,_,_,_);
	//@ chars_to_freelist(x);
	struct freelist* f = (struct freelist*)x;
	f->next = s->free;
	//@ close freelist(f, sz);
	s->free = f;
}

/****************************************************************
 * End
 ****************************************************************/
