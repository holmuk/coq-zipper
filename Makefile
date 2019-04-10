V=@
.PHONY: clean

all: plugin

plugin: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	$(V)coq_makefile -f _CoqProject -o Makefile.coq

clean:
	$Vif [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq clean; fi
	find . -name '*.vo' -print -delete
	find . -name '*.glob' -print -delete
	find . -name *.d -print -delete
	find . -name *.o -print -delete
	find . -name *.bak -print -delete
	find . -name *~ -print -delete
	find . -name *.conflicts -print -delete
	find . -name *.output -print -delete
	find . -name *.aux -print -delete
	rm -f Makefile.coq*
