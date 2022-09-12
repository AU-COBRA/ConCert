all: theory plugin
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
all: theory process-extraction-examples

# Do not forward these files
Makefile _CoqProject: ;

process-extraction-examples: theory plugin
	./process-extraction-examples.sh
.PHONY: process-extraction-examples

LIQUIDITY_DIR=./tests/extracted-code/liquidity-extract
LIQUIDITY_SRC_DIR=$(LIQUIDITY_DIR)/tests
LIQUIDITYFILES=$(wildcard $(LIQUIDITY_SRC_DIR)/*.liq)
LIQUIDITY_DIST=$(patsubst $(LIQUIDITY_SRC_DIR)/%.liq,$(LIQUIDITY_SRC_DIR)/%.tz,$(LIQUIDITYFILES))

LIGO_DIR=./tests/extracted-code/cameligo-extract
LIGO_SRC_DIR=$(LIGO_DIR)/tests
LIGOFILES=$(wildcard $(LIGO_SRC_DIR)/*.mligo)
LIGO_DIST=$(patsubst $(LIGO_SRC_DIR)/%.mligo,$(LIGO_SRC_DIR)/%.tz,$(LIGOFILES))

CONCORDIUM_DIR=./tests/extracted-code/concordium-extract
MIDLANG_DIR=./tests/extracted-code/midlang-extract

RUST_DIR=./tests/extracted-code/rust-extract

ELM_DIR=./tests/extracted-code/elm-extract
ELM_WEB_APP_DIR=./tests/extracted-code/elm-web-extract

test-extraction: test-elm test-liquidity test-ligo test-rust test-concordium

test-concordium: clean-compiled-concordium
	$(foreach dir, $(wildcard $(CONCORDIUM_DIR)/*-extracted), cd $(dir) && cargo concordium test && cd ../../../..;)

test-rust: clean-compiled-rust
	$(foreach dir, $(wildcard $(RUST_DIR)/*-extracted), cd $(dir) && cargo run && cd ../../../..;)

test-elm:
	cd $(ELM_DIR); elm-test
	cd $(ELM_WEB_APP_DIR); elm make src/Main.elm

test-liquidity: clean-compiled-liquidity $(LIQUIDITY_DIST)

$(LIQUIDITY_SRC_DIR)/%.tz:
	liquidity $(LIQUIDITY_SRC_DIR)/$*.liq -o $@ 2>> $(LIQUIDITY_DIR)/liquidity.log

test-ligo: clean-comiped-ligo $(LIGO_DIST)

$(LIGO_SRC_DIR)/%.tz:
	ligo compile contract --protocol jakarta $(LIGO_SRC_DIR)/$*.mligo -e main -o $@ --no-warn

clean-comiped-ligo:
	rm -f ./tests/extracted-code/cameligo-extract/tests/*.tz

clean-compiled-liquidity:
	rm -f ./tests/extracted-code/liquidity-extract/tests/*.tz

clean-compiled-concordium:
	rm -f -r $(CONCORDIUM_DIR)/concert-std/target
	$(foreach dir, $(wildcard $(CONCORDIUM_DIR)/*-extracted), rm -f -r $(dir)/target;)
.PHONY: clean-compiled-concordium

clean-compiled-rust:
	$(foreach dir, $(wildcard $(RUST_DIR)/*-extracted), rm -f -r $(dir)/target;)
.PHONY: clean-compiled-rust

clean-compiled-elm:
	rm -f -r $(ELM_WEB_APP_DIR)/elm-stuff
	rm -f -r $(ELM_WEB_APP_DIR)/index.html
	rm -f -r $(ELM_DIR)/elm-stuff
.PHONY: clean-comliped-elm

clean-compiled-extraction: clean-compiled-elm clean-comiped-ligo clean-compiled-liquidity clean-compiled-rust clean-compiled-concordium
.PHONY: clean-compiled-extraction

clean-extraction-out-files:
	rm -f $(ELM_WEB_APP_DIR)/*.elm.out
	rm -f $(ELM_DIR)/*.elm.out
	rm -f $(LIQUIDITY_DIR)/*.liq.out
	rm -f $(LIGO_DIR)/*.mligo.out
	rm -f $(CONCORDIUM_DIR)/*.rs.out
	rm -f $(MIDLANG_DIR)/*.midlang.out
	rm -f $(RUST_DIR)/*.rs.out
	$(foreach dir, $(wildcard $(CONCORDIUM_DIR)/*-extracted), rm -f -r $(dir)/*.rs.out;)

clean-extraction-sources:
	rm -f $(ELM_DIR)/tests/*.elm
	rm -f $(ELM_WEB_DIR)/src/*.elm
	rm -f $(LIQUIDITY_DIR)/*.liq
	rm -f $(LIGO_DIR)/*.mligo
.PHONY:clean-extraction-sources

clean-extraction-examples: clean-compiled-extraction clean-extraction-out-files clean-extraction-sources
	rm ./tests/*.vo # to force recompilation of examples (a bit ad-hoc though)
.PHONY: clean-extraction-examples clean-comiped-ligo clean-comiped-ligo test-concordium test-elm test-liquidity test-ligo test-extraction clean-extraction-out-files
