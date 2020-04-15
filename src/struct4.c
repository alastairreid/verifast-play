/****************************************************************
 * Experiments in struct wrapping
 *
 * Trying to find a way of supporting the common idiom of
 * defining a struct W with a single field of type T
 *
 *     struct W { T x; };
 *
 * as a type-checkable alternative to writing
 *
 *     typedef T W;
 *
 * Copyright Alastair Reid 2020
 * SPDX-Licence-Identifier: BSD-3-Clause
 ****************************************************************/

#include "stdlib.h"

typedef int T;

//@ predicate MyT(T *t) = *t |-> ?x &*& x > 0;

void incT(T *t)
	//@ requires MyT(t);
	//@ ensures MyT(t);
{
	//@ open MyT(t);
	if (*t < 100) (*t)++;
	//@ close MyT(t);
}

typedef T *W;

#define W_t(w) (w)
#define set_W_t(w, t) (t)

//@ predicate MyW(W w) = MyT(W_t(w));

#if 1
void incW(W w)
	//@ requires MyW(w);
	//@ ensures  MyW(w);
{
	//@ open MyW(w);
	incT(W_t(w));
	//@ close MyW(w);
}
#endif

#if 1
W createW(T *t)
	//@ requires MyT(t);
	//@ ensures  MyW(result);
{
	W w;
	w = set_W_t(w, t);
	//@ close MyW(w);
	return w;
}
#endif

#if 1
T* freeW(W w)
	//@ requires MyW(w);
	//@ ensures  MyT(result);
{
	//@ open MyW(w);
	T *t = W_t(w);
	return t;
}
#endif

#if 1
T* foo(T *t)
	//@ requires MyT(t);
	//@ ensures MyT(result);
{
	W w = createW(t);
	incW(w);
	return freeW(w);
}
#endif

/****************************************************************
 * End
 ****************************************************************/
