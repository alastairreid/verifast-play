VF = verifast/bin/verifast

TESTS =
TESTS += src/list.c
TESTS += src/alist.c
TESTS += src/locktest.c

check::
	$(VF) -c $(TESTS)
