VF = verifast/bin/verifast

TESTS =
TESTS += src/list.c
TESTS += src/alist.c
TESTS += src/locktest.c
TESTS += src/wraptest.c
TESTS += src/malloc0.c

check::
	$(VF) -c $(TESTS)
