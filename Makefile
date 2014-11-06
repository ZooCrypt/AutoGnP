-include Makefile.local

UNAME_S := $(shell uname -s)
ifeq ($(UNAME_S),Linux)
  LIBFLAGS=-lflags -cclib,-Xlinker,-cclib,--no-as-needed,-cclib,-Lc_src,-cclib,-lfactory,-cclib,-lfactorystubs
endif
ifeq ($(UNAME_S),Darwin)
  LIBFLAGS=-lflags -cclib,-Lc_src,-cclib,-lfactory,-cclib,-lfactorystubs
endif

OCAMLBUILDFLAGS=-cflags "-w +a-e-9-44" -use-menhir -menhir "menhir -v" -classic-display -use-ocamlfind

.PHONY : clean all doc test\
  Test_Util Test_Type Test_Expr Test_Norm Test_Cpa Test_Parser Test_Web build-toolchain web

all: wszoocrypt

stubs:
	test -d _build/c_src || mkdir -p _build/c_src
	c++ -fPIC -c c_src/factory_stubs.cc -o _build/c_src/factory_stubs.o -I/usr/local/include/factory
	ar rc _build/c_src/libfactorystubs.a _build/c_src/factory_stubs.o
	c++ -shared -o _build/c_src/libfactorystubs.so _build/c_src/factory_stubs.o -lfactory

stubtest:
	c++ c_src/factory_stubs.cc -o factory_test -I/usr/local/include/factory -DWITHMAIN -lfactory 
	./factory_test

doc:
	ocamlbuild $(OCAMLBUILDFLAGS) tutor.docdir/index.html

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

zoocrypt : stubs
	ocamlbuild $(LIBFLAGS) $(OCAMLBUILDFLAGS) zoocrypt.native

factory : stubs
	ocamlbuild $(LIBFLAGS) $(OCAMLBUILDFLAGS) Factory.native


wszoocrypt : stubs
	ocamlbuild $(LIBFLAGS) $(OCAMLBUILDFLAGS) wszoocrypt.native
	-killall wszoocrypt.native

##########################################################################
# Build PDF from literate program using ocamlweb and pdflatex

UTIL_MODULES= Util/HashconsTypes.ml Util/Hashcons.ml Util/Hashcons.mli \
  Util/Util.ml Util/Util.mli Util/IdType.mli Util/Id.ml Util/Id.mli \
  Util/nondet.ml Util/nondet.mli
POLY_MODULES= Poly/PolyInterfaces.mli Poly/Poly.ml Poly/Poly.mli Poly/PolyInsts.ml 
EXPR_MODULES= Expr/Type.ml Expr/Type.mli Expr/Syms.ml Expr/Syms.mli Expr/Expr.ml Expr/Expr.mli
CAS_MODULES= CAS/LinAlg.ml CAS/LinAlg.mli CAS/CAS.ml CAS/CAS.mli CAS/Factory.ml
SYMBOLIC_MODULES= Symbolic/Norm.ml Symbolic/Norm.mli \
  Symbolic/DeducField.ml Symbolic/DeducField.mli \
  Symbolic/DeducXor.ml Symbolic/DeducXor.mli \
  Symbolic/Deduc.ml  Symbolic/Deduc.mli
GAME_MODULES= Game/Gsyms.ml Game/Gsyms.mli Game/Game.ml Game/Game.mli Game/Wf.ml Game/Wf.mli
LOGIC_MODULES= Logic/Assumption.ml Logic/Assumption.mli Logic/CoreRules.ml Logic/CoreRules.mli \
  Logic/Rules.ml Logic/Rules.mli Logic/CaseRules.ml Logic/CaseRules.mli \
  Logic/RewriteRules.ml Logic/RewriteRules.mli \
  Logic/RandomRules.ml Logic/RandomRules.mli \
  Logic/RindepRules.ml Logic/RindepRules.mli \
  Logic/CrushRules.ml Logic/CrushRules.mli
PARSER_MODULES= Parser/ParserTypes.ml Parser/ParserUtil.ml Parser/ParserUtil.mli Parser/Parse.ml Parser/Parse.mli
TACTIC_MODULES= Tactic/TheoryTypes.ml Tactic/TheoryState.ml Tactic/TheoryState.mli Tactic/Tactic.ml Tactic/Tactic.mli
TOOL_MODULES= Main/zoocrypt.ml Main/wszoocrypt.ml

UTIL_FILES=$(addprefix src/,$(UTIL_MODULES))
POLY_FILES=$(addprefix src/,$(POLY_MODULES))
EXPR_FILES=$(addprefix src/,$(EXPR_MODULES))
CAS_FILES=$(addprefix src/,$(CAS_MODULES))
SYMBOLIC_FILES=$(addprefix src/,$(SYMBOLIC_MODULES))
GAME_FILES=$(addprefix src/,$(GAME_MODULES))
LOGIC_FILES=$(addprefix src/,$(LOGIC_MODULES))
PARSER_FILES=$(addprefix src/,$(PARSER_MODULES))
TACTIC_FILES=$(addprefix src/,$(TACTIC_MODULES))
TOOL_FILES=$(addprefix src/,$(TOOL_MODULES))

ldoc:
	ocamlweb doc/prelude.tex \
	  doc/chap-util.tex $(UTIL_FILES) \
	  doc/chap-poly.tex $(POLY_FILES) \
	  doc/chap-expr.tex $(EXPR_FILES) \
	  doc/chap-cas.tex $(CAS_FILES) \
	  doc/chap-symbolic.tex $(SYMBOLIC_FILES) \
	  doc/chap-game.tex $(GAME_FILES) \
	  doc/chap-logic.tex $(LOGIC_FILES) \
	  doc/chap-parser.tex $(PARSER_FILES) \
	  doc/chap-tactic.tex $(TACTIC_FILES) \
	  doc/chap-tool.tex $(TOOL_FILES) \
	  doc/close.tex --no-preamble --header > doc/tool.tex.tmp

	echo "\end{document}" >> doc/tool.tex.tmp
	mv doc/tool.tex.tmp doc/tool.tex
	cd doc && latexmk -pdf tool.tex

UTIL_IFILES=src/Util/HashconsTypes.ml $(filter %.mli,$(UTIL_FILES)) 
POLY_IFILES=$(filter %.mli,$(POLY_FILES))
EXPR_IFILES=$(filter %.mli,$(EXPR_FILES))
CAS_IFILES=$(filter %.mli,$(CAS_FILES))
SYMBOLIC_IFILES=$(filter %.mli,$(SYMBOLIC_FILES))
GAME_IFILES=$(filter %.mli,$(GAME_FILES))
LOGIC_IFILES=src/Logic/CoreTypes.ml $(filter %.mli,$(LOGIC_FILES))
PARSER_IFILES=$(filter %.mli,$(PARSER_FILES))
TACTIC_IFILES=src/Tactic/TheoryTypes.ml $(filter %.mli,$(TACTIC_FILES))

ldoci:
	ocamlweb doc/prelude.tex \
	  doc/chap-util.tex $(UTIL_IFILES) \
	  doc/chap-poly.tex $(POLY_IFILES) \
	  doc/chap-expr.tex $(EXPR_IFILES) \
	  doc/chap-cas.tex $(CAS_IFILES) \
	  doc/chap-symbolic.tex $(SYMBOLIC_IFILES) \
	  doc/chap-game.tex $(GAME_IFILES) \
	  doc/chap-logic.tex $(LOGIC_IFILES) \
	  doc/chap-parser.tex $(PARSER_IFILES) \
	  doc/chap-tactic.tex $(TACTIC_IFILES) \
	  doc/close.tex --no-preamble --header > doc/tooli.tex.tmp

	echo "\end{document}" >> doc/tooli.tex.tmp
	mv doc/tooli.tex.tmp doc/tooli.tex
	cd doc && latexmk -pdf tooli.tex

UTIL_LFILES=$(filter-out %.mli,$(UTIL_FILES)) 
POLY_LFILES=$(filter-out %.mli,$(POLY_FILES))
EXPR_LFILES=$(filter-out %.mli,$(EXPR_FILES))
CAS_LFILES=$(filter-out %.mli,$(CAS_FILES))
SYMBOLIC_LFILES=$(filter-out %.mli,$(SYMBOLIC_FILES))
GAME_LFILES=$(filter-out %.mli,$(GAME_FILES))
LOGIC_LFILES=$(filter-out %.mli,$(LOGIC_FILES))
PARSER_LFILES=$(filter-out %.mli,$(PARSER_FILES))
TACTIC_LFILES=$(filter-out %.mli,$(TACTIC_FILES))
TOOL_LFILES=$(filter-out %.mli,$(TOOL_FILES))

ldocl:
	ocamlweb doc/prelude.tex \
	  doc/chap-util.tex $(UTIL_LFILES) \
	  doc/chap-poly.tex $(POLY_LFILES) \
	  doc/chap-expr.tex $(EXPR_LFILES) \
	  doc/chap-cas.tex $(CAS_LFILES) \
	  doc/chap-symbolic.tex $(SYMBOLIC_LFILES) \
	  doc/chap-game.tex $(GAME_LFILES) \
	  doc/chap-logic.tex $(LOGIC_LFILES) \
	  doc/chap-parser.tex $(PARSER_LFILES) \
	  doc/chap-tactic.tex $(TACTIC_LFILES) \
	  doc/chap-tool.tex $(TOOL_FILES) \
	  doc/close.tex --no-preamble --header > doc/tooll.tex.tmp

	echo "\end{document}" >> doc/tooll.tex.tmp
	mv doc/tooll.tex.tmp doc/tooll.tex
	cd doc && latexmk -pdf tooll.tex

##########################################################################
# Used for development and testing

test-examples: zoocrypt
	sh scripts/run_tests.sh

test-examples-ec: zoocrypt
	sh scripts/run_tests_ec.sh

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
