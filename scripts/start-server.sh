#/bin/sh

test -f /scripts/activate-toolchain.sh && eval `./scripts/activate-toolchain.sh`
ocsigenserver -c ./etc/ocsigen.conf