all: examples process-extraction-examples
.PHONY: all

RocqMakefile: _CoqProject
	rocq makefile -f _CoqProject -o RocqMakefile

examples: RocqMakefile
	+@make -f RocqMakefile
.PHONY: examples

clean: RocqMakefile
	+@make -f RocqMakefile clean
	rm -f RocqMakefile
.PHONY: clean

install: RocqMakefile
	+@make -f RocqMakefile install
.PHONY: install

uninstall: RocqMakefile
	+@make -f RocqMakefile uninstall
.PHONY: uninstall

vos: RocqMakefile
	+@make -f RocqMakefile vos

quick: RocqMakefile
	+@make -f RocqMakefile COQEXTRAFLAGS="-unset \"Universe Checking\"" vos

# Forward most things to Rocq makefile. Use 'force' to make this phony.
%: RocqMakefile force
	+@make -f RocqMakefile $@
force: ;

# Do not forward these files
Makefile _CoqProject: ;

process-extraction-examples: examples
	cd ../extraction && ./process-extraction-examples.sh
.PHONY: process-extraction-examples
