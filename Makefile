

OCAMLBUILDFLAGS=-cflags "-w +a-e-9" -use-menhir -menhir "menhir -v" -classic-display -use-ocamlfind

.PHONY : clean all doc\
  Test_Util Test_Type Test_Expr Test_Norm Test_Cpa Test_Parser Test_Web build-toolchain web


cur-dir := $(shell pwd)
opam-root := $(shell opam config var root)


all: zoocrypt

doc:
	ocamlbuild $(OCAMLBUILDFLAGS) tutor.docdir/index.html

tutor-lib:
	ocamlbuild $(OCAMLBUILDFLAGS) tutor.cma

web:
	ocamlbuild $(OCAMLBUILDFLAGS) tutor.cma
	mkdir -p data/log/ocsigenserver
	mkdir -p data/lib/ocsigenserver
	mkdir -p data/ocsign/extensions/ocsidbm
	sed -e "s,%%PREFIX%%,$(cur-dir)," -e "s,%%OPAM%%,$(opam-root)," etc/ocsigen.conf.in > etc/ocsigen.conf

toolchain:
	./scripts/build-toolchain

update-toolchain:
	$$(./scripts/activate-toolchain.sh) \
	&& opam update  -y \
	&& opam upgrade -y  \
	&& opam install -y eliom ounit yojson menhir

clean:
	ocamlbuild -clean
	-@rm -rf tutor.docdir


##########################################################################
# Used for development and testing

Test_Type :
	ocamlbuild $(OCAMLBUILDFLAGS) Test_Type.d.byte && ./Test_Type.d.byte

Test_Expr :
	ocamlbuild $(OCAMLBUILDFLAGS) Test_Expr.d.byte && ./Test_Expr.d.byte

Test_Singular :
	ocamlbuild $(OCAMLBUILDFLAGS) Test_Singular.d.byte && ./Test_Singular.d.byte

Test_Proof_BB1 :
	ocamlbuild $(OCAMLBUILDFLAGS) Test_Proof_BB1.d.byte && ./Test_Proof_BB1.d.byte

Test_Wf :
	ocamlbuild $(OCAMLBUILDFLAGS) Test_Wf.d.byte && ./Test_Wf.d.byte

Test_Pretty_Expr :
	ocamlbuild $(OCAMLBUILDFLAGS) Test_Pretty_Expr.d.byte && ./Test_Pretty_Expr.d.byte

Test_Parser :
	ocamlbuild $(OCAMLBUILDFLAGS) Test_Parser.d.byte && ./Test_Parser.d.byte

Test_Proofsearch :
	ocamlbuild $(OCAMLBUILDFLAGS) Test_Proofsearch.d.byte && ./Test_Proofsearch.d.byte

zoocrypt :
	ocamlbuild $(OCAMLBUILDFLAGS) zoocrypt.native && ./zoocrypt.native ./examples/bb1.zc

%.inferred.mli:
	ocamlbuild $(OCAMLBUILDFLAGS) src/$@ && cat _build/src/$@
