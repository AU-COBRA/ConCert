EXTRA_DIR:=extra
DOCS_DIR:=docs
COQDOCFLAGS:= \
  --html --interpolate \
  --no-index --no-lib-name --parse-comments \
  --with-header $(EXTRA_DIR)/header.html --with-footer $(EXTRA_DIR)/footer.html
export COQDOCFLAGS
COQMAKEFILE:=CoqMakefile
COQ_PROJ:=_CoqProject
ELM_DIR:=./extraction/examples/elm-extract/
LIQ_DIR:=./extraction/examples/liquidity-extract/tests


default: code process-extraction

all: code html

code: $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE)

clean: $(COQMAKEFILE)
	@$(MAKE) -f $(COQMAKEFILE) $@
	rm -f $(COQMAKEFILE)

html: $(COQMAKEFILE)
	rm -rf $(DOCS_DIR)
	@$(MAKE) -f $(COQMAKEFILE) $@
	cp $(EXTRA_DIR)/resources/* html
	mv html $(DOCS_DIR)

$(COQMAKEFILE): $(COQ_PROJ)
		coq_makefile -f $(COQ_PROJ) -o $@

%: $(COQMAKEFILE) force
	@$(MAKE) -f $(COQMAKEFILE) $@
force $(COQ_PROJ): ;

test-extraction:
	cd $(ELM_DIR); elm-test
	$(foreach file, $(wildcard $(LIQ_DIR)/*.liq), liquidity $(file);)

process-extraction: code
	./process-extraction.sh

clean-extraction:
	rm ./extraction/examples/elm-extract/*.elm.out
	rm ./extraction/examples/liquidity-extract/*.liq.out

.PHONY: clean all default force
