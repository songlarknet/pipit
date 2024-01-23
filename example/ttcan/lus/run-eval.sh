#!/bin/bash
# Tabulate TTCAN verification runtimes up to nth power-of-two.
# Run from Pipit docker. Usage:
# > docker run pipit example/ttcan/lus/run-eval.sh 3
# Generates to `build/tmp.report` with 3 array sizes (1, 2, 4)

if [ "$#" -ne 1 ]; then
  echo "Usage: $0 <count>"
  echo "  where <count> dictates how many tests to run"
  exit 1
fi
COUNT=$1


TIME_FORMAT='--format=%es&%Us'
OUT_REPORT=build/tmp.report

mkdir -p build
echo '' > $OUT_REPORT

rm build/cache/Network.TTCan.TriggerTimely.fst.checked
/usr/bin/time -o build/tmp.time $TIME_FORMAT make build/cache/Network.TTCan.TriggerTimely.fst.checked
PIPIT_RUNTIME=$(cat build/tmp.time)
echo "*** Pipit took: " $PIPIT_RUNTIME

ROW_END="$PIPIT_RUNTIME"


function run_test {
  local inc=$1
  local count=$2
  cat <<EOF > build/tmp.lus
const TRIGGERS_COUNT: int = $count;
include "$inc"
EOF
  /usr/bin/time -o build/tmp.time $TIME_FORMAT kind2 --modular true --compositional true build/tmp.lus
  OK=$?
  if [ $OK = 0 ]; then
    cat build/tmp.time >> $OUT_REPORT
    echo "*** Kind2 row $count took $(cat build/tmp.time)"
  else
    printf " \multicolumn{2}{c|}{error} " >> $OUT_REPORT
    echo "*** Kind2 row $count ERROR"
  fi
}


function row {
  local count=$1
  printf "****** Row $count ******"
  printf " $count & " >> $OUT_REPORT
  run_test ../example/ttcan/lus/trigger_simple_enable.lus $count
  printf  " & " >> $OUT_REPORT
  run_test ../example/ttcan/lus/trigger_full_enable.lus $count
  printf " & $ROW_END \\\\\\\\" >> $OUT_REPORT
  printf "\n" >> $OUT_REPORT
}


POW2=1
for (( i = 0; i < $COUNT; ++i )); do
  row $POW2
  POW2=$(($POW2 * 2))
done

echo
echo "****** Report ******"
echo
cat $OUT_REPORT
