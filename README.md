# C(++) libraries

To get the required C(++) library, follow these instructions.

1. download and install NTL from
http://www.shoup.net/ntl/ntl-6.2.1.tar.gz

cd src
./configure NTL_GMP_LIP=on SHARED=on
sudo make install
(on OS X, you have to install glibtool (e.g., using homebrew) and use
 ./configure NTL_GMP_LIP=on SHARED=on LIBTOOL="glibtool --tag" )

2. download and install libfactory from
http://www.mathematik.uni-kl.de/ftp/pub/Math/Factory/factory-4.0.1.tar.gz

./configure --disable-streamio --without-Singular --disable-static
sudo make install

# Ocaml libraries

It is probably easiest to install the following ocaml dependencies
using the opam manager for OCaml (see http://opam.ocamlpro.com/):
- ounit
- yojson
- websocket
- ctypes
- ctypes-foreign
- bolt
- ... (and their dependencies)


# Compile ZooCrypt

Then, the websocket server can be compiled
with 'make wszoocrypt' and the batch tool
can be compiled with .

# Examples

The examples can be found in 'examples/ok'.

They can stepped through using a web interface
by executing './wszoocrypt.native file' and following
the instructions.

They can be all executed by running 'make test-examples'.
This also creates the EasyCrypt 'ec' files in extraction.
These files can be checked with the bundled version of
EasyCrypt

# Limitations

Extraction for the Waters'09 examples is not enabled since
the support for extracting Hybrid arguments is still
incomplete.