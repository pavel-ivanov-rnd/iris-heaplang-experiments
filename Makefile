%: Makefile.coq phony
	+@make -f Makefile.coq $@

# Compile this project
all: Makefile.coq
	+@make -f Makefile.coq all

clean: Makefile.coq
	+@make -f Makefile.coq clean
	rm -f Makefile.coq

Makefile.coq: _CoqProject Makefile
	coq_makefile -f _CoqProject | sed 's/$$(COQCHK) $$(COQCHKFLAGS) $$(COQLIBS)/$$(COQCHK) $$(COQCHKFLAGS) $$(subst -Q,-R,$$(COQLIBS))/' > Makefile.coq

# Initialize local Iris dependency
iris-local-init: clean
	git submodule update --init iris
	ln -nsf iris iris-enabled

# Build local Iris dependency
iris-local:
	+make -C iris -f Makefile

# Initialize global Iris dependency
iris-system-init: clean
	rm -f iris-enabled

# Update local Iris dependency
iris-local-update:
	git submodule update --remote --merge


_CoqProject: ;

Makefile: ;

phony: ;

.PHONY: all clean phony iris-local iris-local-init iris-system-init

