all: examples process-extraction-examples
.PHONY: all

CoqMakefile: _CoqProject
	coq_makefile -f _CoqProject -o CoqMakefile

examples: CoqMakefile
	+@make -f CoqMakefile
.PHONY: examples

clean: CoqMakefile
	+@make -f CoqMakefile clean
	rm -f CoqMakefile
.PHONY: clean

install: CoqMakefile
	+@make -f CoqMakefile install
.PHONY: install

uninstall: CoqMakefile
	+@make -f CoqMakefile uninstall
.PHONY: uninstall

vos: CoqMakefile
	+@make -f CoqMakefile vos

quick: CoqMakefile
	+@make -f CoqMakefile COQEXTRAFLAGS="-unset \"Universe Checking\"" vos

# Forward most things to Coq makefile. Use 'force' to make this phony.
%: CoqMakefile force
	+@make -f CoqMakefile $@
force: ;

# Do not forward these files
Makefile _CoqProject: ;

process-extraction-examples: examples
	cd ../extraction && ./process-extraction-examples.sh
.PHONY: process-extraction-examples
