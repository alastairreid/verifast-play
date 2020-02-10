/****************************************************************
 * Experiments with casting between types of different sizes
 * without losing track of the original size.
 *
 * Copyright Alastair Reid 2020
 * SPDX-Licence-Identifier: BSD-3-Clause
 ****************************************************************/

#include "stdlib.h"
#include "stdint.h"
#include "malloc.h"

struct S {
	uint32_t s;
};

struct T {
	uint64_t t;
};

// To cast back and forth between pointers to different types,
// we need to pad the objects to some size that is at least
// as big as either of the types.
#define SIZE (sizeof(struct S) <= sizeof(struct T) ? sizeof(struct T) : sizeof(struct S))

/*@

predicate isPaddedS(struct S* s;) =
	s->s |-> _
	&*& struct_S_padding(s)
	&*& chars((void*)s + sizeof(struct S), SIZE - sizeof(struct S), _)
;

predicate isPaddedT(struct T* t;) =
	t->t |-> _
	&*& struct_T_padding(t)
	&*& chars((void*)t + sizeof(struct T), SIZE - sizeof(struct T), _)
;

@*/

/****************************************************************
 * Constructors for S and T
 ****************************************************************/

struct S* mkS()
	//@ requires true;
	//@ ensures isPaddedS(result) &*& malloc_block(result, SIZE);
{
	void *c = malloc(SIZE);
	if (c == 0) abort();
	//@ chars_split(c, sizeof(struct S));
	struct S* s = (struct S*)c;
	//@ close_struct(s);
	return s;
}

struct T* mkT()
	//@ requires true;
	//@ ensures isPaddedT(result) &*& malloc_block(result, SIZE);
{
	void *c = malloc(SIZE);
	if (c == 0) abort();
	//@ chars_split(c, sizeof(struct T));
	struct T* t = (struct T*)c;
	//@ close_struct(t);
	return t;
}

/****************************************************************
 * Conversions between S and T
 ****************************************************************/

struct S* t_to_s(struct T* t)
	//@ requires isPaddedT(t);
	//@ ensures  isPaddedS(result);
{
	//@ open_struct(t);
	//@ chars_join((void*)t);
	void *c = t;
	//@ chars_split(c, sizeof(struct S));
	struct S* s = (struct S*)c;
	//@ close_struct(s);
	return s;
}

struct T* s_to_t(struct S* s)
	//@ requires isPaddedS(s);
	//@ ensures  isPaddedT(result);
{
	//@ open_struct(s);
	//@ chars_join((void*)s);
	void *c = s;
	//@ chars_split(c, sizeof(struct T));
	struct T* t = (struct T*)c;
	//@ close_struct(t);
	return t;
}

/****************************************************************
 * Sequential tests
 ****************************************************************/

// Sequential test code
void test_padding()
	//@ requires true;
	//@ ensures  true;
{
	struct S *s = mkS();
	struct T *t = mkT();

	struct T *pt = s_to_t(s);
	struct S *ps = t_to_s(t);

	//@ leak isPaddedS(ps);
	//@ leak isPaddedT(pt);
	//@ leak malloc_block(s, _);
	//@ leak malloc_block(t, _);
}

/****************************************************************
 * End
 ****************************************************************/
