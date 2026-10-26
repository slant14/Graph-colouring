# Build the verified certificate checker: extract Certificate.v to OCaml and
# compile it with the small parsing driver main.ml.
#   make            (needs the Rocq development built: cd .. && make)
all: certcheck

certcheck.ml certcheck.mli: Extract.v ../Certificate.vo
	coqc -Q .. CertCol Extract.v

certcheck: certcheck.mli certcheck.ml main.ml
	ocamlfind ocamlopt -O3 certcheck.mli certcheck.ml main.ml -o certcheck

clean:
	rm -f certcheck *.cm* *.o certcheck.ml certcheck.mli Extract.vo Extract.vok Extract.vos Extract.glob .Extract.aux

.PHONY: all clean
