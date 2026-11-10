# Build, check and test apgar.v with Rocq 9.0 and OCaml.
#
#   make        compile apgar.v; any compiler output fails the build
#   make check  re-check the compiled library with rocqchk
#   make test   compile the extracted OCaml and run test/smoke.ml
#   make ci     all three

ROCQ ?= rocq
ROCQCHK ?= rocqchk
OCAMLC ?= ocamlc
OCAMLRUN ?= ocamlrun

.PHONY: all check test ci clean

all: apgar.vo

# Compiling apgar.v also writes the extraction, apgar.ml and apgar.mli.
apgar.vo: apgar.v
	$(ROCQ) compile -Q . Apgar apgar.v > build.log 2>&1 || (cat build.log; exit 1)
	@if [ -s build.log ]; then cat build.log; exit 1; fi

# rocqchk re-checks every proof term with a separate kernel and prints the
# axioms of the checked context; the target fails if any is listed.
check: apgar.vo
	$(ROCQCHK) -o -silent -Q . Apgar Apgar.apgar > rocqchk.log 2>&1 || (cat rocqchk.log; exit 1)
	@cat rocqchk.log
	@grep -q "Axioms: <none>" rocqchk.log

test: apgar.vo
	$(OCAMLC) -c apgar.mli
	$(OCAMLC) -c apgar.ml
	$(OCAMLC) -I . -o smoke.byte apgar.cmo test/smoke.ml
	$(OCAMLRUN) smoke.byte

ci: all check test

clean:
	rm -f apgar.vo apgar.vok apgar.vos apgar.glob .apgar.aux .lia.cache
	rm -f apgar.ml apgar.mli apgar.cmi apgar.cmo smoke.byte
	rm -f test/smoke.cmi test/smoke.cmo build.log rocqchk.log
