#!/bin/sh
# Script to test the set of current examples

VERBOSE=no
if [ "$1" = "-v" ] ; then
  VERBOSE=yes
fi

# Tool executable:
TOOLBIN=currvy
# Tool options:
OPTS="--strict --no-failfree"

/bin/rm -rf .curry
ECODE=0
FAILEDTESTS=

for p in *.curry ; do
  if [ $VERBOSE = yes ] ; then
    $TOOLBIN $OPTS $p 2>&1 | tee test.out
  else
    $TOOLBIN $OPTS $p > test.out 2>&1
  fi
  SC=`grep -c SPIO_E_NET_CONNRESET test.out` # check for internal SICStus error
  if [ $SC -gt 0 ] ; then
     if [ $VERBOSE = yes ] ; then
       echo "WARNING: test of $p ignored due to internal SICStus error."
     fi
  elif [ "`tail -1 test.out`" != "ALL CONTRACTS VERIFIED!" ] ; then
    echo "$p: FULL VERIFICATION FAILED!"
    FAILEDTESTS="$FAILEDTESTS $p"
    ECODE=1
  fi
  rm test.out
done
if [ $ECODE -gt 0 ] ; then
  echo "FAILURES OCCCURRED IN SOME TESTS:$FAILEDTESTS"
  exit $ECODE
elif [ $VERBOSE = yes ] ; then
  echo "All tests successfully executed!"
fi
