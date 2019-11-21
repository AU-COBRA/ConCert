EXTRA_DIR:=../extra
DOCS_DIR:=docs
COQDOCFLAGS:= \
  --html --interpolate \
  --no-index --no-lib-name --parse-comments \
  --with-header $(EXTRA_DIR)/header.html --with-footer $(EXTRA_DIR)/footer.html
export COQDOCFLAGS
COQMAKEFILE:=CoqMakefile
COQ_PROJ:=_CoqProject

default: code

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

.PHONY: clean all default force
