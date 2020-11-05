#!/usr/bin/env bash

if [[ ! -f "plugin/src/concert_extraction_plugin.cmxs" ||
      "plugin/src/concert_extraction_plugin.cmxs" -ot "theories/ExtractExtraction.vo" ]]
then
  cd plugin/src
  # Uncapitalize modules to circumvent a bug of coqdep with mlpack files
  for i in *.ml*
  do
    newi=`echo $i | cut -b 1 | tr '[:upper:]' '[:lower:]'``echo $i | cut -b 2-`;
    if [[ ! $i -ef $newi ]]
    then
      echo "Moving " $i "to" $newi;
      mv $i $newi;
    fi
  done

  # This file was generated with
  # cat template-coq/_PluginProject | grep "^[^#].*mli\?$" | sed "s/gen-src\///"
  # from MetaCoq root
  files=`cat ../template-coq-files.txt`
  echo "Removing files linked in template-coq:" $files
  rm -f $files

  echo "Fixing extraction bugs"
  sed -i "s/Coq__2/Coq__1/g" common1.mli
  sed -i "s/Coq__3/Coq__1/g" common1.mli
else
  echo "Extraction up to date"
fi
