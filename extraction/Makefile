all: theory
.PHONY: all

CoqMakefile: _CoqProject
	coq_makefile -f _CoqProject -o CoqMakefile

theory: CoqMakefile
	+@make -f CoqMakefile
.PHONY: theory

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
all: theory process-extraction-examples

# Do not forward these files
Makefile _CoqProject: ;

process-extraction-examples: theory
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

test-extraction: test-liquidity test-ligo test-concordium

test-concordium: clean-compiled-concordium
	$(foreach dir, $(wildcard $(CONCORDIUM_DIR)/*-extracted), cd $(dir) && cargo concordium test && cd ../../../..;)

test-liquidity: clean-compiled-liquidity $(LIQUIDITY_DIST)

$(LIQUIDITY_SRC_DIR)/%.tz:
	liquidity $(LIQUIDITY_SRC_DIR)/$*.liq -o $@ 2>> $(LIQUIDITY_DIR)/liquidity.log

test-ligo: clean-comiped-ligo $(LIGO_DIST)

$(LIGO_SRC_DIR)/%.tz:
	ligo compile contract --protocol kathmandu $(LIGO_SRC_DIR)/$*.mligo -e main -o $@ --no-warn

clean-comiped-ligo:
	rm -f ./tests/extracted-code/cameligo-extract/tests/*.tz

clean-compiled-liquidity:
	rm -f ./tests/extracted-code/liquidity-extract/tests/*.tz

clean-compiled-concordium:
	rm -f -r $(CONCORDIUM_DIR)/concert-std/target
	$(foreach dir, $(wildcard $(CONCORDIUM_DIR)/*-extracted), rm -f -r $(dir)/target;)
.PHONY: clean-compiled-concordium

clean-compiled-extraction: clean-comiped-ligo clean-compiled-liquidity clean-compiled-concordium
.PHONY: clean-compiled-extraction

clean-extraction-out-files:
	rm -f $(LIQUIDITY_DIR)/*.liq.out
	rm -f $(LIGO_DIR)/*.mligo.out
	rm -f $(CONCORDIUM_DIR)/*.rs.out
	rm -f $(MIDLANG_DIR)/*.midlang.out
	$(foreach dir, $(wildcard $(CONCORDIUM_DIR)/*-extracted), rm -f -r $(dir)/*.rs.out;)

clean-extraction-sources:
	rm -f $(LIQUIDITY_DIR)/tests/*.liq
	rm -f $(LIQUIDITY_DIR)/liquidity.log
	rm -f $(LIGO_DIR)/tests/*.mligo
	rm -f $(MIDLANG_DIR)/tests/*.midlang
	$(foreach dir, $(wildcard $(CONCORDIUM_DIR)/*-extracted), rm -f $(dir)/src/lib.rs;)
.PHONY:clean-extraction-sources

clean-extraction-examples: clean-compiled-extraction clean-extraction-out-files clean-extraction-sources
	rm ./tests/*.vo # to force recompilation of examples (a bit ad-hoc though)
.PHONY: clean-extraction-examples clean-comiped-ligo clean-comiped-ligo test-concordium test-liquidity test-ligo test-extraction clean-extraction-out-files
