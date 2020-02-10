/****************************************************************
 * Wraparound arithmetic library
 *
 * VeriFast's truncating add seems to be an
 * uninterpreted function so I wrote my own.
 *
 * Copyright Alastair Reid 2020
 * SPDX-Licence-Identifier: BSD-3-Clause
 ****************************************************************/

#include "stdint.h"

uint64_t wrap_add64(uint64_t x, uint64_t y)
	//@ requires true;
	/*@
	    ensures
		(x + y) <= UINT64_MAX
		?
			result == (x + y)
		:
			result == (x + y) - (UINT64_MAX + 1)
		;
	@*/
{
	uint128_t r1 = (uint128_t)x + (uint128_t)y;
	uint64_t r = (uint64_t)(r1 <= UINT64_MAX ? r1 : (r1 - UINT64_MAX - 1u));
	return r;
}

// Unsigned version of UINT64_MAX == 2^64-1
#define myUINT64_MAX 18446744073709551615u

// 2^63
#define myUINT64_HALF 9223372036854775808u

uint64_t wrap_sub64(uint64_t x, uint64_t y)
	//@ requires true;
	/*@
	    ensures
		x >= y
		?
			result == (x - y)
		:
			result == (x - y) + UINT64_MAX + 1
		;
	@*/
{
	if (x >= y) {
		return x-y;
	} else if (y <= INT64_MAX) { // y <= INT64_MAX && x < y
		uint64_t y1 = (myUINT64_MAX - y) + 1u;
		return (x + y1);
	} else if (x > INT64_MAX) { // x > INT64_MAX && y > INT64_MAX && x < y
		return (x - (y - myUINT64_HALF)) + myUINT64_HALF;
	} else { // x <= INT64_MAX && y > INT64_MAX && x > y
		return (x + myUINT64_HALF) - (y - myUINT64_HALF);
	}
}

/****************************************************************
 * End
 ****************************************************************/
