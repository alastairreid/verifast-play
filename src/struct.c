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

struct W {
	T t;
};

#if 1
// Produces this error
//   Dereferencing pointers of type struct W is not yet supported.
T w_to_t(struct W w)
	//@ requires true;
	//@  ensures true;
	// The following 'ensures' clause is not allowed. Produces this error:
	//   Taking the address of this expression is not supported.
	// ensures  result == w.t;
{
	return w.t;
}
#endif

#if 0
// Produces this error
//   Cannot consume points-to chunk for variable of type 'struct W'
struct W t_to_w(T t)
	//@ requires true;
	//@ ensures  true;
	// ensures  result.t == t;
{
	struct W w;
	w.t = t;
	return w;
}
#endif

/****************************************************************
 * Typedef experiments
 *
 * (These do not make any difference)
 ****************************************************************/

typedef struct W W_t;

#if 0
// Produces this error
//   Dereferencing pointers of type struct W is not yet supported.
T w_to_t2(W_t w)
	//@ requires true;
	//@ ensures true;
{
	return w.t;
}
#endif

/****************************************************************
 * End
 ****************************************************************/
