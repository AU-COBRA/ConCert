#!/bin/bash

ELM_PATH=./extraction/examples/elm-extract
LIQ_PATH=./extraction/examples/liquidity-extract
ELM_TESTS=$ELM_PATH/tests
LIQ_TESTS=$LIQ_PATH/tests

rm $ELM_TESTS/*.elm
rm $LIQ_TESTS/*.liq
rm $LIQ_TESTS/*.tz

echo "Processing Elm extraction"
for f in $ELM_PATH/*.elm.out;
do
    echo $f "--->" $ELM_TESTS/$(basename ${f%.out}) ;
    sed -n 's/ *"//;/module/,/suite/p' $f > $ELM_TESTS/$(basename ${f%.out})
done

echo "Processing Liquidity extraction"
for f in $LIQ_PATH/*.liq.out;
do
    echo $f "--->" $LIQ_TESTS/$(basename ${f%.out}) ;
    sed -n 's/ *"//;/\(*START*\)/,/\(*END*\)/p' $f > $LIQ_TESTS/$(basename ${f%.out})
done
