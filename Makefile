-include Makefile.local

OCAMLBUILDFLAGS=-cflags "-w +a-e-9" -use-menhir -menhir "menhir -v" -classic-display -use-ocamlfind

.PHONY : clean all doc test\
  Test_Util Test_Type Test_Expr Test_Norm Test_Cpa Test_Parser Test_Web build-toolchain web

UTIL_MODULES= Util/HashconsTypes.ml Util/Hashcons.ml Util/Hashcons.mli \
  Util/Util.ml Util/Util.mli Util/IdType.mli Util/Id.ml Util/Id.mli
EXPR_MODULES=Expr/Type.ml Expr/Type.mli Expr/Syms.ml Expr/Syms.mli Expr/Expr.ml Expr/Expr.mli
CAS_MODULES=CAS/LinAlg.ml CAS/LinAlg.mli CAS/Poly.ml CAS/Poly.mli CAS/CAS.ml CAS/CAS.mli
SYMBOLIC_MODULES=Symbolic/Norm.ml Symbolic/Norm.mli Symbolic/DeducField.ml Symbolic/DeducField.mli \
  Symbolic/DeducXor.ml Symbolic/DeducXor.mli Symbolic/Deduc.ml  Symbolic/Deduc.mli
GAME_MODULES=Game/Gsyms.ml Game/GSyms.mli Game/Game.ml Game/Game.mli Game/Wf.ml Game/Wf.mli
LOGIC_MODULES=Logic/Assumption.ml Logic/Assumption.mli Logic/CoreRules.ml Logic/CoreRules.mli \
  Logic/Rules.ml Logic/Rules.mli
PARSER_MODULES=Parser/ParserUtil.ml Parser/ParserUtil.mli Parser/Parse.ml Parser/Parse.mli
TACTIC_MODULES=Tactic/TheoryState.ml Tactic/TheoryState.mli Tactic/Tactic.ml Tactic/Tactic.mli

UTIL_FILES=$(addprefix src/,$(UTIL_MODULES))
EXPR_FILES=$(addprefix src/,$(EXPR_MODULES))
CAS_FILES=$(addprefix src/,$(CAS_MODULES))
SYMBOLIC_FILES=$(addprefix src/,$(SYMBOLIC_MODULES))
GAME_FILES=$(addprefix src/,$(GAME_MODULES))
LOGIC_FILES=$(addprefix src/,$(LOGIC_MODULES))
PARSER_FILES=$(addprefix src/,$(PARSER_MODULES))
TACTIC_FILES=$(addprefix src/,$(TACTIC_MODULES))

cur-dir := $(shell pwd)

all: wszoocrypt

doc:
	ocamlbuild $(OCAMLBUILDFLAGS) tutor.docdir/index.html

ldoc:
	ocamlweb doc/prelude.tex \
	  doc/chap-util.tex $(UTIL_FILES) \
	  doc/chap-expr.tex $(EXPR_FILES) \
	  doc/chap-cas.tex $(CAS_FILES) \
	  doc/chap-symbolic.tex $(SYMBOLIC_FILES) \
	  doc/chap-game.tex $(GAME_FILES) \
	  doc/chap-logic.tex $(LOGIC_FILES) \
	  doc/chap-parser.tex $(PARSER_FILES) \
	  doc/chap-tactic.tex $(TACTIC_FILES) \
	  doc/close.tex --no-preamble --header > doc/tool.tex.tmp
	echo "\end{document}" >> doc/tool.tex.tmp
	mv doc/tool.tex.tmp doc/tool.tex
	cd doc && latexmk -pdf tool.tex


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
	ocamlbuild $(OCAMLBUILDFLAGS) zoocrypt.native

wszoocrypt :
	ocamlbuild $(OCAMLBUILDFLAGS) wszoocrypt.native 

##########################################################################
# Used for development and testing

test-examples: zoocrypt
	for file in examples/ok/*.zc examples/extr_fail/*.zc; do\
	   printf "\e[1;32mFile $$file: \n";\
	   /usr/bin/time sh -c "./zoocrypt.native $$file  2>&1 | grep --colour=always -i -e 'Finished Proof' -e 'EasyCrypt proof script.extracted'" ;\
	done

Test_Type :
	ocamlbuild $(OCAMLBUILDFLAGS) Test_Type.d.byte && ./Test_Type.d.byte

Test_Expr :
	ocamlbuild $(OCAMLBUILDFLAGS) Test_Expr.d.byte && ./Test_Expr.d.byte

Test_Singular :
	ocamlbuild $(OCAMLBUILDFLAGS) Test_Singular.d.byte && ./Test_Singular.d.byte

Test_Pretty_Expr :
	ocamlbuild $(OCAMLBUILDFLAGS) Test_Pretty_Expr.d.byte && ./Test_Pretty_Expr.d.byte

Test_Solve_Fq :
	ocamlbuild $(OCAMLBUILDFLAGS) Test_Solve_Fq.d.byte && ./Test_Solve_Fq.d.byte


test: zoocrypt
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

%.inferred.mli:
	ocamlbuild $(OCAMLBUILDFLAGS) src/$@ && cat _build/src/$@
