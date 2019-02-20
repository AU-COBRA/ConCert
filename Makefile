# Based on makefile from Iris.
# Forward most targets to Coq makefile (with some trick to make this phony)
%: CoqMakefile phony
	+@make -f CoqMakefile $@

all: CoqMakefile
	+@make -f CoqMakefile all
.PHONY: all

clean: CoqMakefile
	+@make -f CoqMakefile clean
	rm -f CoqMakefile
.PHONY: clean

# Create Coq Makefile.
CoqMakefile: _CoqProject Makefile
	"$(COQBIN)coq_makefile" -f _CoqProject -o CoqMakefile

# Some files that do *not* need to be forwarded to Makefile.coq
Makefile: ;
_CoqProject: ;
opam: ;

# Phony wildcard targets
phony: ;
.PHONY: phony
