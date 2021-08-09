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
		-R embedding/theories ConCert.Embedding \
		-R extraction/theories ConCert.Extraction \
		-d docs `find . -type f -wholename "*theories/*" -name "*.v"`
	cp extra/resources/* docs
.PHONY: html
