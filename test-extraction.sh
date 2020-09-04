#!/bin/bash

ELM_PATH=./extraction/examples/elm-extract
ELM_TESTS=$ELM_PATH/tests

rm $ELM_TESTS/*.elm

for f in $ELM_PATH/*.elm.out;
do
    echo $f "--->" $ELM_TESTS/$(basename ${f%.out}) ;
    sed -n 's/ *"//;/module/,/suite/p' $f > $ELM_TESTS/$(basename ${f%.out})
done

cd $ELM_PATH
elm-test
