all: utils execution embedding extraction
.PHONY: all

utils:
	+make -C utils
.PHONY: utils

execution: utils
	+make -C execution
.PHONY: execution

embedding: utils execution
	+make -C embedding
.PHONY: embedding

extraction: utils execution
	+make -C extraction
.PHONY: extraction

examples: utils execution embedding extraction
	+make -C examples
.PHONY: examples

clean:
	+make -C utils clean
	+make -C execution clean
	+make -C embedding clean
	+make -C extraction clean
	+make -C examples clean
	rm -rf docs
.PHONY: clean

install: all
	+make -C utils install
	+make -C execution install
	+make -C embedding install
	+make -C extraction install
.PHONY: install

uninstall: all
	+make -C utils uninstall
	+make -C execution uninstall
	+make -C embedding uninstall
	+make -C extraction uninstall
.PHONY: uninstall

test-extraction:
	+make -C extraction test-extraction
.PHONY: test-extraction

process-extraction-examples:
	+make -C extraction process-extraction-examples
.PHONY: process-extraction-examples


clean-extraction-out-files:
	+make -C extraction clean-extraction-out-files
.PHONY: clean-extraction-out-files

clean-compiled-extraction:
	+make -C extraction clean-compiled-extraction
.PHONY:clean-compiled-extraction

clean-extraction-examples:
	+make -C extraction clean-extraction-examples
.PHONY: clean-extraction-examples

html: all
	rm -rf docs
	mkdir docs
	coqdoc --html --interpolate --parse-comments \
		--with-header extra/header.html --with-footer extra/footer.html \
		--toc \
		-R utils/theories ConCert.Utils \
		-R execution/theories ConCert.Execution \
		-R execution/test ConCert.Execution.Test \
		-R embedding/theories ConCert.Embedding \
		-R embedding/extraction ConCert.Embedding.Extraction \
		-R embedding/examples ConCert.Embedding.Examples \
		-R extraction/theories ConCert.Extraction \
		-R extraction/plugin/theories ConCert.Extraction \
		-R extraction/tests ConCert.Extraction.Tests \
		-R examples ConCert.Examples \
		-d docs `find . -type f \( -wholename "*theories/*" -o -wholename "*examples/*" -o -wholename "*extraction/*" -o -wholename "*test/*" \) -name "*.v"`
	cp extra/resources/coqdocjs/*.js docs
	cp extra/resources/coqdocjs/*.css docs
	cp extra/resources/toc/*.js docs
	cp extra/resources/toc/*.css docs

.PHONY: html
