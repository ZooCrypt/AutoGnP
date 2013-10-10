

OCAMLBUILDFLAGS=-cflags "-w +a-e-9" -use-menhir -menhir "menhir -v" -classic-display -use-ocamlfind

.PHONY : clean all doc\
  Test_Util Test_Type Test_Expr Test_Norm Test_Cpa Test_Parser Test_Web build-toolchain web


cur-dir := $(shell pwd)
opam-root := $(shell opam config var root)


all: Test_Expr

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
	-@rm -rf synth.docdir


##########################################################################
# Used for development and testing

start-server : web
	./scripts/start-server.sh

Test_Util : 
	ocamlbuild $(OCAMLBUILDFLAGS) Test_Util.d.byte && ./Test_Util.d.byte

Test_Type : 
	ocamlbuild $(OCAMLBUILDFLAGS) Test_Type.d.byte && ./Test_Type.d.byte

Test_Expr : 
	ocamlbuild $(OCAMLBUILDFLAGS) Test_Expr.d.byte && ./Test_Expr.d.byte

Test_Norm : 
	ocamlbuild $(OCAMLBUILDFLAGS) Test_Norm.d.byte && ./Test_Norm.d.byte

Test_Deducibility : 
	ocamlbuild $(OCAMLBUILDFLAGS) Test_Deducibility.d.byte && ./Test_Deducibility.d.byte

Test_Cpa : 
	ocamlbuild $(OCAMLBUILDFLAGS) Test_Cpa.d.byte && OCAMLRUNPARAM="-b" ./Test_Cpa.d.byte

Test_Parser : 
	ocamlbuild $(OCAMLBUILDFLAGS) Test_Parser.d.byte && OCAMLRUNPARAM="-b" ./Test_Parser.d.byte

Test_Bound : 
	ocamlbuild $(OCAMLBUILDFLAGS) Test_Bound.d.byte && OCAMLRUNPARAM="-b" ./Test_Bound.d.byte

Test_Web :
	ocamlbuild $(OCAMLBUILDFLAGS) Test_Web.d.byte && (killall ocamlrun; OCAMLRUNPARAM="-b" ./Test_Web.d.byte)

%.inferred.mli:
	ocamlbuild $(OCAMLBUILDFLAGS) src/$@ && cat _build/src/$@
