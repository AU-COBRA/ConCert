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

uninstall:
	+make -C utils uninstall
	+make -C execution uninstall
	+make -C embedding uninstall
	+make -C extraction uninstall

vos:
	+make -C utils vos
	+make -C execution vos
	+make -C embedding vos
	+make -C extraction vos
	+make -C examples vos

quick:
	+make -C utils quick
	+make -C execution quick
	+make -C embedding quick
	+make -C extraction quick
	+make -C examples quick

QuickChick: examples
	+make -C examples QuickChick

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
.PHONY: clean-compiled-extraction

clean-extraction-examples:
	+make -C extraction clean-extraction-examples
.PHONY: clean-extraction-examples

dependency-graphs: utils execution embedding extraction examples
	+make -C utils dep-graphs-svg
	+make -C execution dep-graphs-svg
	+make -C embedding dep-graphs-svg
	+make -C extraction dep-graphs-svg
	+make -C examples dep-graphs-svg

file-dependency-graph:
	@echo "Generate dot files"
	@coqdep -dumpgraph utils-file-dep.dot -f utils/_CoqProject >/dev/null 2>&1
	@coqdep -dumpgraph execution-file-dep.dot -f execution/_CoqProject >/dev/null 2>&1
	@coqdep -dumpgraph embedding-file-dep.dot -f embedding/_CoqProject >/dev/null 2>&1
	@coqdep -dumpgraph extraction-file-dep.dot -f extraction/_CoqProject >/dev/null 2>&1
	@coqdep -dumpgraph examples-file-dep.dot -f examples/_CoqProject >/dev/null 2>&1

	@echo "Add node colors"
	@sed -i.tmp 's/"\]/", style=filled, fillcolor="#FFC09F"\]/' utils-file-dep.dot ; rm -f utils-file-dep.dot.tmp
	@sed -i.tmp 's/"\]/", style=filled, fillcolor="#FFEE93"\]/' execution-file-dep.dot ; rm -f execution-file-dep.dot.tmp
	@sed -i.tmp 's/"\]/", style=filled, fillcolor="#FCF5C7"\]/' embedding-file-dep.dot ; rm -f embedding-file-dep.dot.tmp
	@sed -i.tmp 's/"\]/", style=filled, fillcolor="#A0CED9"\]/' extraction-file-dep.dot ; rm -f extraction-file-dep.dot.tmp
	@sed -i.tmp 's/"\]/", style=filled, fillcolor="#ADF7B6"\]/' examples-file-dep.dot ; rm -f examples-file-dep.dot.tmp

	@echo "Fix paths"
	@sed -i.tmp 's/"[^"^\/]*\/\.\.\//"/g' utils-file-dep.dot ; rm -f utils-file-dep.dot.tmp
	@sed -i.tmp 's/"[^"^\/]*\/\.\.\//"/g' execution-file-dep.dot ; rm -f execution-file-dep.dot.tmp
	@sed -i.tmp 's/"[^"^\/]*\/\.\.\//"/g' embedding-file-dep.dot ; rm -f embedding-file-dep.dot.tmp
	@sed -i.tmp 's/"[^"^\/]*\/\.\.\//"/g' extraction-file-dep.dot ; rm -f extraction-file-dep.dot.tmp
	@sed -i.tmp 's/"[^"^\/]*\/\.\.\//"/g' examples-file-dep.dot ; rm -f examples-file-dep.dot.tmp

	@echo "Merge files"
	@dep_utils=$$(cat utils-file-dep.dot | cut -d "{" -f2 | cut -d "}" -f1); \
	dep_execution=$$(cat execution-file-dep.dot | cut -d "{" -f2 | cut -d "}" -f1); \
	dep_embedding=$$(cat embedding-file-dep.dot | cut -d "{" -f2 | cut -d "}" -f1); \
	dep_extraction=$$(cat extraction-file-dep.dot | cut -d "{" -f2 | cut -d "}" -f1); \
	dep_examples=$$(cat examples-file-dep.dot | cut -d "{" -f2 | cut -d "}" -f1); \
	rm -f utils-file-dep.dot execution-file-dep.dot embedding-file-dep.dot extraction-file-dep.dot examples-file-dep.dot; \
	echo "digraph dependencies {$${dep_utils}$${dep_execution}$${dep_embedding}$${dep_extraction}$${dep_examples}\n}" > file-dep.dot

	@echo "Remove duplicates"
	@awk '!seen[$$0]++' file-dep.dot > file-dep.tmp; mv file-dep.tmp file-dep.dot

	@echo "Convert to SVG"
	@dot -Tsvg -o file-dep.svg file-dep.dot ; rm -f file-dep.dot

html: all
	rm -rf docs
	mkdir docs
	coqdoc --html --interpolate --parse-comments \
		--with-header extra/header.html --with-footer extra/footer.html \
		--toc \
		--external https://plv.mpi-sws.org/coqdoc/stdpp stdpp \
		--external https://metacoq.github.io/html MetaCoq \
		--external https://coq-community.org/coq-ext-lib/v0.11.7 ExtLib \
		-R utils/theories ConCert.Utils \
		-R execution/theories ConCert.Execution \
		-R execution/test ConCert.Execution.Test \
		-R embedding/theories ConCert.Embedding \
		-R embedding/extraction ConCert.Embedding.Extraction \
		-R embedding/examples ConCert.Embedding.Examples \
		-R extraction/theories ConCert.Extraction \
		-R extraction/tests ConCert.Extraction.Tests \
		-R examples/eip20 ConCert.Examples.EIP20 \
		-R examples/bat ConCert.Examples.BAT \
		-R examples/fa2 ConCert.Examples.FA2 \
		-R examples/fa1_2 ConCert.Examples.FA1_2 \
		-R examples/dexter ConCert.Examples.Dexter \
		-R examples/dexter2 ConCert.Examples.Dexter2 \
		-R examples/exchangeBuggy ConCert.Examples.ExchangeBuggy \
		-R examples/iTokenBuggy ConCert.Examples.iTokenBuggy \
		-R examples/cis1 ConCert.Examples.CIS1 \
		-R examples/stackInterpreter ConCert.Examples.StackInterpreter \
		-R examples/congress ConCert.Examples.Congress \
		-R examples/escrow ConCert.Examples.Escrow \
		-R examples/boardroomVoting ConCert.Examples.BoardroomVoting \
		-R examples/counter ConCert.Examples.Counter \
		-R examples/crowdfunding ConCert.Examples.Crowdfunding \
		-R examples/piggybank ConCert.Examples.PiggyBank \
		-d docs `find . -type f \( -wholename "*theories/*" -o -wholename "*examples/*" -o -wholename "*extraction/*" -o -wholename "*test/*" \) -name "*.v" ! -name "AllTests.v" ! -wholename "./_opam/*"`
	cp extra/resources/coqdocjs/*.js docs
	cp extra/resources/coqdocjs/*.css docs
	cp extra/resources/toc/*.js docs
	cp extra/resources/toc/*.css docs
.PHONY: html
