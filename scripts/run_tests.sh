#! /bin/bash

function ok_tests() {
  echo 
  echo "*******************************************************************"
  echo "Running examples and ok tests!"
  echo

  FAILED=""
  OK=""
  for file in examples/ok/*.zc; do
    printf "File $file: \n"
    before=$(date +%s)
    if ! ./zoocrypt.native $file 2>&1 | \
         grep --colour=always -i \
           -e 'Finished Proof' -e 'EasyCrypt proof script.extracted'; then
      FAILED="$FAILED $file"
    else
      OK="$OK `basename $file`"
    fi
    after=$(date +%s)
    dt=$((after - before))
    printf  "  \e[1;32m$dt seconds\e[1;0m\n"
  done

  echo "\nFailed: $FAILED"
  echo "\nOK: $OK"
}

function fail_tests() {
  echo
  echo
  echo "*******************************************************************"
  echo "Running mustfail tests!"
  echo

  FAILED=""
  OK=""
  for file in test/fail/*.zc; do
    ERR=`grep ERROR $file | sed 's/ERROR: //'`
    printf "Testing $file, expecting error ''$ERR''\n"  
    if ! ./zoocrypt.native $file 2>&1 | \
         grep -F "$ERR"; then
      FAILED="$FAILED $file"
    else
      OK="$OK $file"
    fi
  done
  echo "\nFailed: $FAILED"
  echo "\nOK: $OK"
}

ok_tests
fail_tests

