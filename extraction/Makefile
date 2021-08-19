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

LIQUIDITY_SRC_DIR=./examples/extracted-code/liquidity-extract/tests
LIQUIDITYFILES=$(wildcard $(LIQUIDITY_SRC_DIR)/*.liq)
LIQUIDITY_DIST=$(patsubst $(LIQUIDITY_SRC_DIR)/%.liq,$(LIQUIDITY_SRC_DIR)/%.tz,$(LIQUIDITYFILES))

LIGO_SRC_DIR=./examples/extracted-code/cameligo-extract/tests
LIGOFILES=$(wildcard $(LIGO_SRC_DIR)/*.mligo)
LIGO_DIST=$(patsubst $(LIGO_SRC_DIR)/%.mligo,$(LIGO_SRC_DIR)/%.tz,$(LIGOFILES))

test-extraction: test-elm test-liquidity test-ligo test-concordium

test-concordium:
	$(foreach dir, $(wildcard ./examples/extracted-code/concordium-extract/*-extracted), cd $(dir) && cargo concordium test && cd ../../../..;)

test-elm:
	cd ./examples/extracted-code/elm-extract/; elm-test
	cd ./examples/extracted-code/elm-web-extract/; elm make src/Main.elm

test-liquidity: clean-compiled-liquidity $(LIQUIDITY_DIST)

$(LIQUIDITY_SRC_DIR)/%.tz:
	liquidity $(LIQUIDITY_SRC_DIR)/$*.liq -o $@


test-ligo: clean-comiped-ligo $(LIGO_DIST)

$(LIGO_SRC_DIR)/%.tz:
	ligo compile-contract $(LIGO_SRC_DIR)/$*.mligo main --output-file=$@ --warn=false

clean-comiped-ligo:
	rm ./examples/extracted-code/cameligo-extract/tests/*.tz -f

clean-compiled-liquidity:
	rm ./examples/extracted-code/liquidity-extract/tests/*.tz -f

clean-extraction-out-files:
	rm ./examples/extracted-code/elm-extract/*.elm.out -f
	rm ./examples/extracted-code/liquidity-extract/*.liq.out -f
	rm ./examples/extracted-code/cameligo-extract/*.mligo.out -f
	rm ./examples/extracted-code/concordium-extract/*.rs.out -f
	rm ./examples/extracted-code/rust-extract/*.rs.out -f
	rm ./examples/extracted-code/midlang-extract/*.midlang.out -f

clean-extraction-examples: clean-comiped-ligo clean-compiled-liquidity clean-extraction-out-files
	rm ./examples/extracted-code/elm-extract/tests/*.elm
	rm ./examples/extracted-code/liquidity-extract/tests/*.liq
	rm ./examples/extracted-code/cameligo-extract/tests/*.mligo


.PHONY: clean-extraction-examples clean-comiped-ligo clean-comiped-ligo test-concordium test-elm test-liquidity test-ligo test-extraction
