#!/usr/bin/env bash
make
FILES=$(find . -type f -iname "*.v" -exec basename {} .v ';')
IMP="From ConCert.Execution Require ${FILES}. Require dpdgraph.dpdgraph. Print FileDependGraph ${FILES}."

echo $IMP | coqtop -R ../vendor/record-update RecordUpdate -R theories ConCert.Execution
