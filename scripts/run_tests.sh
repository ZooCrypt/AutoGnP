#! /bin/sh

FAILED=""
for file in examples/ok/*.zc examples/extr_fail/*.zc; do
  printf "File $file: \n"
  before=$(date +%s)
  if ! ./zoocrypt.native $file 2>&1 | grep --colour=always -i -e 'Finished Proof' -e 'EasyCrypt proof script.extracted'; then
    FAILED="$FAILED $file"
  fi
  after=$(date +%s)
  dt=$((after - before))
  printf  "  \e[1;32m$dt seconds\e[1;0m\n"
done

echo "\nFailed: $FAILED"
