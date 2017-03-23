MODULES := \
	src/GBCompute.v \
	src/GBZArith.v
NAME := GBArith
ROOT := ./
.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(MODULES)
	coq_makefile \
	-I $(ROOT)src \
	-Q $(ROOT)src $(NAME) \
	$(MODULES) -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq .depend
