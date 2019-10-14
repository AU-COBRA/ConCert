EXTRA_DIR:=extra
TARGET_DIR:=docs
COQDOCFLAGS:= \
  --html --interpolate \
  --no-index --no-lib-name --parse-comments \
  --with-header $(EXTRA_DIR)/header.html --with-footer $(EXTRA_DIR)/footer.html
export COQDOCFLAGS
COQMAKEFILE:=Makefile.coq
COQ_PROJ:=_CoqProject

all: html

code: Makefile.coq
	$(MAKE) -f Makefile.coq

clean: $(COQMAKEFILE)
	@$(MAKE) -f $(COQMAKEFILE) $@
	rm -f $(COQMAKEFILE)

html: $(COQMAKEFILE)
	rm -fr $(TARGET_DIR)
	@$(MAKE) -f $(COQMAKEFILE) $@
	cp $(EXTRA_DIR)/resources/* html
	mv html docs

$(COQMAKEFILE): $(COQ_PROJ)
		coq_makefile -f $(COQ_PROJ) -o $@

%: $(COQMAKEFILE) force
	@$(MAKE) -f $(COQMAKEFILE) $@
force $(COQ_PROJ): ;

.PHONY: clean all force
