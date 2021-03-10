#!/bin/bash

ELM_PATH=./examples/elm-extract
ELM_WEB_PATH=./examples/elm-web-extract
LIQ_PATH=./examples/liquidity-extract
MID_PATH=./examples/midlang-extract
ELM_TESTS=$ELM_PATH/tests
ELM_WEB_SRC=$ELM_WEB_PATH/src
LIQ_TESTS=$LIQ_PATH/tests
MID_TESTS=$MID_PATH/tests

rm $ELM_TESTS/*.elm
rm $LIQ_TESTS/*.liq
rm $LIQ_TESTS/*.tz
rm $MID_TESTS/*.midlang

echo "Processing Elm extraction"
for f in $ELM_PATH/*.elm.out;
do
    echo $f "--->" $ELM_TESTS/$(basename ${f%.out}) ;
    sed -n 's/ *"//;/module/,/suite/p' $f > $ELM_TESTS/$(basename ${f%.out})
done

WEB_APP_OUT=UserList.elm.out

echo "Processing Elm web-app extraction"
echo $WEB_APP_OUT "+ views.elm"  "--->" $ELM_WEB_SRC/Main.elm;
cat $ELM_WEB_PATH/$WEB_APP_OUT $ELM_WEB_SRC/views.elm > $ELM_WEB_SRC/Main.elm


echo "Processing Liquidity extraction"
for f in $LIQ_PATH/*.liq.out;
do
    echo $f "--->" $LIQ_TESTS/$(basename ${f%.out}) ;
    sed -n 's/ *"//;/\(*START*\)/,/\(*END*\)/p' $f > $LIQ_TESTS/$(basename ${f%.out})
done

echo "Processing Midlang extraction"
for f in $MID_PATH/*.midlang.out;
do
    echo $f "--->" $MID_TESTS/$(basename ${f%.out}) ;
    cp $f $MID_TESTS/$(basename ${f%.out})
done
