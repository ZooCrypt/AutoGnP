

OCAMLBUILDFLAGS=-cflags "-w +a-e-9" -use-menhir -menhir "menhir -v" -classic-display -use-ocamlfind

.PHONY : clean all doc\
  Test_Util Test_Type Test_Expr Test_Norm Test_Cpa Test_Parser Test_Web build-toolchain web


cur-dir := $(shell pwd)
opam-root := $(shell opam config var root)


all: wszoocrypt

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
	&& opam install -y ounit yojson websocket

clean:
	ocamlbuild -clean
	-@rm -rf tutor.docdir

zoocrypt :
	ocamlbuild $(OCAMLBUILDFLAGS) zoocrypt.native && ./zoocrypt.native ./examples/bb1_asym.zc

wszoocrypt :
	ocamlbuild $(OCAMLBUILDFLAGS) wszoocrypt.native 

##########################################################################
# Used for development and testing

Test_Type :
	ocamlbuild $(OCAMLBUILDFLAGS) Test_Type.d.byte && ./Test_Type.d.byte

Test_Expr :
	ocamlbuild $(OCAMLBUILDFLAGS) Test_Expr.d.byte && ./Test_Expr.d.byte

Test_Singular :
	ocamlbuild $(OCAMLBUILDFLAGS) Test_Singular.d.byte && ./Test_Singular.d.byte

Test_Pretty_Expr :
	ocamlbuild $(OCAMLBUILDFLAGS) Test_Pretty_Expr.d.byte && ./Test_Pretty_Expr.d.byte

all-tests: zoocrypt
	@echo "============ OK TESTS ==============="
	@for file in test/rules/ok/*.zc; do\
	   printf "File $$file:\n";\
	   ./zoocrypt.native $$file;\
	 done
	@echo "============ FAILING TESTS ==============="
	@for file in test/rules/fail/*.zc; do\
	  printf "File $$file:\n";\
	  ./zoocrypt.native $$file;\
	   echo ;\
	 done

macaulay:
	m2 --no-tvalues --no-tty --no-prompts --silent ./scripts/test.m2

%.inferred.mli:
	ocamlbuild $(OCAMLBUILDFLAGS) src/$@ && cat _build/src/$@
