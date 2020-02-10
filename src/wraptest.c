/****************************************************************
 * Tests for Wraparound arithmetic library
 *
 * Copyright Alastair Reid 2020
 * SPDX-Licence-Identifier: BSD-3-Clause
 ****************************************************************/

#include "wrap.h"

/****************************************************************
 * Tests
 *
 * These functions are not expected to be called - their purpose
 * is to confirm that wrapping add/sub obey some basic arithmetic
 * axioms.
 *
 * I think that it would also be possible to write these as lemmas
 * but I hope that those lemmas would never be needed so these are
 * just a sanity check that the wrapping arithmetic ops behave as
 * expected.
 ****************************************************************/

void test_addsub64_1(uint64_t x)
	//@ requires true;
	//@ ensures  true;
	//@ terminates;
{
	uint64_t a = wrap_add64(x, 0);
	//@ assert(a == x);

	uint64_t b = wrap_sub64(x, 0);
	//@ assert(b == x);

	uint64_t c = wrap_add64(x, 1);
	//@ assert(c != x);

	uint64_t d = wrap_sub64(x, 1);
	//@ assert(d != x);

	uint64_t e = wrap_sub64(wrap_add64(x, 1), 1);
	//@ assert(e == x);

	uint64_t f = wrap_sub64(x, x);
	//@ assert(f == 0);

	uint64_t g = wrap_sub64(0, wrap_sub64(0, x));
	//@ assert(g == x);
}

void test_addsub64_2(uint64_t x, uint64_t y)
	//@ requires true;
	//@ ensures  true;
	//@ terminates;
{
	uint64_t a1 = wrap_add64(x, y);
	uint64_t a2 = wrap_add64(y, x);
	//@ assert(a1 == a2);

	uint64_t b1 = wrap_sub64(x, y);
	uint64_t b2 = wrap_sub64(0, wrap_sub64(y, x));
	//@ assert(b1 == b2);
}

/****************************************************************
 * End
 ****************************************************************/
