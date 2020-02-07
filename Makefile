VF = verifast/bin/verifast

TESTS =
TESTS += src/list.c
TESTS += src/alist.c

check::
	$(VF) -c $(TESTS)
