All required software can be locally installed in
the source directory using 'make toolchain'.

Note that on debian, the following packages must
be installed:
  curl libssl-dev make libpcre3-dev m4

Then, the webserver can be compiled with 'make'.

It is also possible to use a global Ocaml
installation and install the libraries eliom,
yojson, menhir, and ounit yourself, e.g., using the
opam package package manager for OCaml
(see http://opam.ocamlpro.com/).

You also need an installation of macaulay2 [1] which
is used for field simplification, solving of linear
equations, and ideal computations.

It is available on:
  http://www.math.uiuc.edu/Macaulay2/Downloads/


[1] http://www.math.uiuc.edu/Macaulay2/


OUTDATED (for now, we only use macaulay2).

You need an installation of singular [1] to use
the field simplification.

On mac, you can just download
  ftp://www.mathematik.uni-kl.de/pub/Math/Singular/UNIX/Singular-3-1-6-ix86Mac-darwin.tar.gz
and
  ftp://www.mathematik.uni-kl.de/pub/Math/Singular/UNIX/Singular-3-1-6-share.tar.gz
and follow the installation instructions on:
  http://www.singular.uni-kl.de/index.php/singular-download/109.html
After the installation is finished, you should be able to start "Singular"
from the commandline.

[1] http://www.singular.uni-kl.de/