# Toolchain

Most required software can be locally installed in
the source directory using 'make toolchain'.

Note that on debian, the following packages must
be installed:
  curl libssl-dev make libpcre3-dev m4

# C(++) libraries

To get the required C(++) library, follow these instructions.

1. download and install NTL from
http://www.shoup.net/ntl/ntl-6.2.1.tar.gz

cd src
./configure NTL_GMP_LIP=on SHARED=on
sudo make install
(make sure to use libtool from ocamlbrew, this should be glibtool
 installed as /usr/local/bin/libtool)

2. download and install libfactory from
http://www.mathematik.uni-kl.de/ftp/pub/Math/Factory/factory-4.0.1.tar.gz

./configure --disable-streamio --without-Singular --disable-static
sudo make install

# Compile ZooCrypt

Then, the websocket server can be compiled
with 'make'.

It is also possible to use a global Ocaml
installation and install the following libraries
yourself, e.g., using the opam package package
manager for OCaml (see http://opam.ocamlpro.com/):
- ounit
- yojson
- websocket
- ctypes
- ... (and their dependencies)
