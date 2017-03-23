MODULES := \
	src/polyop.mli \
	src/polyop.ml \
	src/polyop_tactic.ml4 \
	src/polyop_plugin_mod.ml \
	src/polyop_plugin.mllib \
	src/PolyOp.v \
	src/Modp.v
NAME := PolyOp
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
