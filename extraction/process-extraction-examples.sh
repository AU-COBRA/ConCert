#!/bin/bash

ELM_PATH=./tests/extracted-code/elm-extract
ELM_WEB_PATH=./tests/extracted-code/elm-web-extract
LIQ_PATH=./tests/extracted-code/liquidity-extract
LIGO_PATH=./tests/extracted-code/cameligo-extract
MID_PATH=./tests/extracted-code/midlang-extract
CONCORDIUM_PATH=./tests/extracted-code/concordium-extract
ELM_TESTS=$ELM_PATH/tests
ELM_WEB_SRC=$ELM_WEB_PATH/src
LIQ_TESTS=$LIQ_PATH/tests
LIGO_TESTS=$LIGO_PATH/tests
MID_TESTS=$MID_PATH/tests

echo "Processing Elm extraction"
for f in $ELM_PATH/*.elm.out;
do
    if [[ ! -e "$f" ]]; then continue; fi
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
    if [[ ! -e "$f" ]]; then continue; fi 
    echo $f "--->" $LIQ_TESTS/$(basename ${f%.out}) ;
    sed -n 's/ *"//;/\(*START*\)/,/\(*END*\)/p' $f > $LIQ_TESTS/$(basename ${f%.out})
done

echo "Processing LIGO extraction"
for f in $LIGO_PATH/*.mligo.out;
do
    if [[ ! -e "$f" ]]; then continue; fi
    echo $f "--->" $LIGO_TESTS/$(basename ${f%.out}) ;
    cp ${f} $LIGO_TESTS/$(basename ${f%.out})
done


echo "Processing Midlang extraction"
for f in $MID_PATH/*.midlang.out;
do
    if [[ ! -e "$f" ]]; then continue; fi
    echo $f "--->" $MID_TESTS/$(basename ${f%.out}) ;
    cp $f $MID_TESTS/$(basename ${f%.out})
done

echo "Processing Rust Concordium extraction"
concordium_contracts="counter interp escrow"

CONCORDIUM_SUFFIX=extracted/src/lib.rs
CONCORDIUM_TESTS=extracted/src/tests.rs

for f in ${concordium_contracts}
do
    if [[ ! -e "$CONCORDIUM_PATH/${f}.rs.out" ]]; then continue; fi
    fname=$CONCORDIUM_PATH/${f}-${CONCORDIUM_SUFFIX}
    echo "removing previous extraction: " ${fname}
    rm -f ${fname}
    echo "Processing ${CONCORDIUM_PATH}/${f}.rs.out + tests.rs --> ${fname}"
    cat $CONCORDIUM_PATH/${f}.rs.out $CONCORDIUM_PATH/${f}-${CONCORDIUM_TESTS} > ${fname}
done
