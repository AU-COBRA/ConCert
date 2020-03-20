SED = `which gsed || which sed`
EXTRA_DIR:=extra
DOCS_DIR:=docs
COQDOCFLAGS:= \
  --html --interpolate \
  --no-index --no-lib-name --parse-comments \
  --with-header $(EXTRA_DIR)/header.html --with-footer $(EXTRA_DIR)/footer.html
export COQDOCFLAGS
COQMAKEFILE:=CoqMakefile
PLUGINMAKEFILE:=CoqMakefile.plugin
COQ_PROJ:=_CoqProject
PLUGIN_PROJ:=_PluginProject

default: code # plugin

all: code html # plugin

plugin: $(PLUGINMAKEFILE)
	$(MAKE) -f $(PLUGINMAKEFILE)

cleanplugin: $(PLUGINMAKEFILE)
	@$(MAKE) -f $(PLUGINMAKEFILE) clean
	rm -f $(PLUGINMAKEFILE)

code: $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE)
#	./clean_extraction.sh

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

$(PLUGINMAKEFILE): $(PLUGIN_PROJ)
		coq_makefile -f $(PLUGIN_PROJ) -o $@ $(DEPS)
		$(SED) -i -e s/coqdeps/coqdeps.plugin/g $(PLUGINMAKEFILE)

%: $(COQMAKEFILE) force
	@$(MAKE) -f $(COQMAKEFILE) $@
force $(COQ_PROJ): ;

.PHONY: clean all default force
