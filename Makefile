DESTDIR    ?=
PREFIX     ?= /usr/local
VERSION    ?= $(shell date '+%F')
INSTALL    := scripts/install/install-sh
PWD        := $(shell pwd)

BINDIR := $(PREFIX)/bin
LIBDIR := $(PREFIX)/lib/autognp
SHRDIR := $(PREFIX)/share/autognp

INSTALL    := scripts/install/install-sh

#############################################################################

UNAME_S := $(shell uname -s)
ifeq ($(UNAME_S),Linux)
  LIBFLAGS=-lflags -cclib,-Xlinker,-cclib,--no-as-needed,-cclib,-Lc_src,-cclib,-lfactory,-cclib,-lfactorystubs
endif
ifeq ($(UNAME_S),Darwin)
  LIBFLAGS=-lflags -cclib,-Lc_src,-cclib,-lfactory,-cclib,-lfactorystubs
endif

OCAMLBUILDFLAGS=-cflags "-w +a-e-9-44-48-37" -use-menhir -menhir "menhir -v" -use-ocamlfind

ifeq ($(shell echo $$TERM), dumb)
 OCAMLBUILDFLAGS += -classic-display -quiet
endif

#############################################################################

.PHONY : clean all doc test autognp.native wsautognp.native test autognp wsautognp \
  Test_Util Test_Type Test_Expr Test_Norm Test_Cpa Test_Parser Test_Web build-toolchain web

all: autognp.native

autognp.native : stubs
	ocamlbuild $(LIBFLAGS) $(OCAMLBUILDFLAGS) autognp.native

stubs:
	@test -d _build/c_src || mkdir -p _build/c_src
	@c++ -fPIC -c c_src/factory_stubs.cc -o _build/c_src/factory_stubs.o -I/usr/local/include/factory
	@ar rc _build/c_src/libfactorystubs.a _build/c_src/factory_stubs.o
	@c++ -shared -o _build/c_src/libfactorystubs.so _build/c_src/factory_stubs.o -lfactory

install:
	$(INSTALL) -m 0755 -d $(DESTDIR)$(BINDIR)
	$(INSTALL) -m 0755 -T autognp.native $(DESTDIR)$(BINDIR)/autognp

uninstall:
	rm -f $(DESTDIR)$(BINDIR)/autognp

clean:
	ocamlbuild -clean
	-@rm -rf tutor.docdir

factory : stubs
	ocamlbuild $(LIBFLAGS) $(OCAMLBUILDFLAGS) Factory.native

wsautognp.native : stubs
	ocamlbuild $(LIBFLAGS) $(OCAMLBUILDFLAGS) wsautognp.native

##########################################################################
# Used for development and testing

dev : stubs
	ocamlbuild $(LIBFLAGS) $(OCAMLBUILDFLAGS) Game.cma

dev_server : wsautognp.native
	-@ killall wsautognp.native

%.deps :
	ocamlfind ocamldep -package bolt -package batteries -syntax camlp4o \
            -package comparelib.syntax \
            -I src/CAS -I src/Expr -I src/Extract -I src/Game -I src/Deduce -I src/Main \
            -I src/Parser -I src/Poly -I src/Norm -I src/Derived -I src/Core \
            -I src/Engine -I src/Util \
            one-line src/$(basename $@).ml> .depend
	ocamldot .depend > deps.dot
	dot -Tsvg deps.dot >deps.svg

depgraph :
	ocamlfind ocamldep -package bolt -package batteries -syntax camlp4o \
            -package comparelib.syntax \
            -I src/CAS -I src/Expr -I src/Extract -I src/Game -I src/Deduce -I src/Main \
            -I src/Parser -I src/Poly -I src/Norm -I src/Derived -I src/Core \
            -I src/Engine -I src/Util \
            one-line src/**/*.ml src/**/*.mli \
        | grep -v Test | grep -v Extract > .depend
	ocamldot .depend > deps.dot
	dot -Tsvg deps.dot >deps.svg


autognp.native-dev : stubs
	ocamlbuild $(LIBFLAGS) $(OCAMLBUILDFLAGS) autognp.native
	rm autognp.log
	BOLT_CONFIG=log_bolt.config ./autognp.native test.zc ; cat autognp.log

wsautognp.native-dev : wsautognp.native
	-@killall wsautognp.native

test-examples: autognp.native
	bash scripts/run_tests.sh

test-examples-ec: autognp.native
	bash scripts/run_examples_ec.sh

test-tests-ec: autognp.native
	bash scripts/run_tests_ec.sh

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

%.inferred.mli:
	ocamlbuild $(OCAMLBUILDFLAGS) src/$@ && cat _build/src/$@

stubtest:
	c++ c_src/factory_stubs.cc -o factory_test -I/usr/local/include/factory -DWITHMAIN -lfactory 
	./factory_test

