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

extraction: utils execution embedding
	+make -C extraction
.PHONY: extraction

clean:
	+make -C utils clean
	+make -C execution clean
	+make -C embedding clean
	+make -C extraction clean
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
		-R utils/theories ConCert.Utils \
		-R execution/theories ConCert.Execution \
		-R execution/examples ConCert.Execution.Examples \
		-R execution/standards ConCert.Execution.Standards \
		-R embedding/theories ConCert.Embedding \
		-R embedding/examples ConCert.Embedding.Examples \
		-R extraction/theories ConCert.Extraction \
		-R extraction/examples ConCert.Extraction.Examples \
		-d docs `find . -type f \( -wholename "*theories/*" -o -wholename "*examples/*" -o -wholename "*standards/*" \) -name "*.v"`
	cp extra/resources/* docs
.PHONY: html
