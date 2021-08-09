all: theory process-extraction-examples plugin
.PHONY: all

CoqMakefile: _CoqProject
	coq_makefile -f _CoqProject -o CoqMakefile

theory: CoqMakefile
	+@make -f CoqMakefile
.PHONY: theory

clean: CoqMakefile
	+@make -f CoqMakefile clean
	rm -f CoqMakefile
	+@make -C plugin clean
.PHONY: clean

install: CoqMakefile
	+@make -f CoqMakefile install
.PHONY: install

uninstall: CoqMakefile
	+@make -f CoqMakefile uninstall
.PHONY: uninstall

plugin: theory
	+make -C plugin
.PHONY: plugin

# Forward most things to Coq makefile. Use 'force' to make this phony.
%: CoqMakefile force
	+@make -f CoqMakefile $@
force: ;

# Do not forward these files
Makefile _CoqProject: ;

process-extraction-examples: theory
	./process-extraction-examples.sh
.PHONY: process-extraction-examples

test-extraction:
	cd ./examples/extracted-code/elm-extract/; elm-test
	cd ./examples/extracted-code/elm-web-extract/; elm make src/Main.elm
	$(foreach file, $(wildcard ./examples/extracted-code/liquidity-extract/tests/*.liq), liquidity $(file);)
	$(foreach dir, $(wildcard ./examples/extracted-code/concordium-extract/*-extracted), cd $(dir) && cargo concordium test && cd ../../../..;)
	$(foreach file, $(wildcard ./examples/extracted-code/cameligo-extract/tests/*.mligo), ligo compile-contract $(file) main;)
.PHONY: test-extraction

clean-extraction-examples:
	rm ./examples/extracted-code/elm-extract/*.elm.out
	rm ./examples/extracted-code/elm-extract/tests/*.elm
	rm ./examples/extracted-code/liquidity-extract/*.liq.out
	rm ./examples/extracted-code/liquidity-extract/tests/*.liq
	rm ./examples/extracted-code/midlang-extract/*.midlang.out
	rm ./examples/*.vo # to force recompilation of examples (a bit ad-hoc though)
.PHONY: clean-extraction-examples
