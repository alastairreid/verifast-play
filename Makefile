VF = verifast/bin/verifast

TESTS =
TESTS += src/list.c
TESTS += src/list_test.c
TESTS += src/list_generic.c
TESTS += src/list_generic_test.c
TESTS += src/alist.c
TESTS += src/locktest.c
TESTS += src/wraptest.c
TESTS += src/padding.c
TESTS += src/align.c
TESTS += src/malloc0.c
TESTS += src/malloc1.c
TESTS += src/malloctest.c

check::
	$(VF) -c $(TESTS)
