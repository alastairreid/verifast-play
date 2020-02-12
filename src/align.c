/****************************************************************
 * Pointer alignment
 *
 * Experiments in manipulating aligned objects.
 *
 * Copyright Alastair Reid 2020
 * SPDX-Licence-Identifier: BSD-3-Clause
 ****************************************************************/

#include "stddef.h"
#include "stdint.h"
#include "wrap.h"

/****************************************************************
 * Alignment annotations
 ****************************************************************/

// VeriFast does not support alignas or alignof so
// we just define them to do nothing and are forced to treat
// them as documentation.
//
// To compensate for this, we have the 'aligned' predicate

#define alignas(n) /* nothing */
#define alignof(t) /* nothing */

#define is_aligned(p, alignment) (((intptr_t)p) % alignment == 0)

// Alas, it is not possible to use the is_aligned macro to define this predicate.
//@ predicate aligned(void* p, size_t alignment;) = ((intptr_t)p) % alignment == 0;

/****************************************************************
 * Alignment-sensitive functions
 ****************************************************************/

#define PAGE_SIZE 4096

// A dummy function that requires an aligned pointer
void foo(void* p);
	//@ requires aligned(p, PAGE_SIZE);
	//@ ensures  aligned(p, PAGE_SIZE);

/****************************************************************
 * Sequential tests
 ****************************************************************/

// not usable by VeriFast
// static const int TABLE_SIZE = 65536;

// not usable by VeriFast
// #define TABLE_SIZE (PAGE_SIZE * 16)

// Alas, this is the only working variant that I have found.
#define TABLE_SIZE 65536

alignas(PAGE_SIZE) char table[TABLE_SIZE];

void test_align()
	//@ requires true;
	//@ ensures  true;
{
	//@ assume(is_aligned(&table, PAGE_SIZE));
	foo(table);
	foo(table);
}

/****************************************************************
 * End
 ****************************************************************/
