#! /bin/sh

EC_CMD=echo

FAILED=""
for file in examples/ok/*.zc; do
  printf "File $file: \n"
  before=$(date +%s)
  if ! ./zoocrypt.native $file 2>&1 | grep --colour=always -i -e 'Finished Proof' -e 'EasyCrypt proof script.extracted'; then
    FAILED_ZC="$FAILED_ZC $file"
  else
    name=`basename $file`
    ec_file=extraction/${name%.zc}.ec
    if ! $EC_CMD ${ec_file}; then
      FAILED_EC="$FAILED_EC $file"
    fi
  fi
  after=$(date +%s)
  dt=$((after - before))
  printf  "  \e[1;32m$dt seconds\e[1;0m\n"
done

echo "\nFailed ZooCrypt: $FAILED_ZC"
echo "\nFailed EasyCrypt: $FAILED_ZC"
