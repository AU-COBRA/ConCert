#!/usr/bin/env bash

if [[ ! -f "plugin/src/concert_extraction_plugin.cmxs" ||
      "plugin/src/concert_extraction_plugin.cmxs" -ot "theories/ExtractExtraction.vo" ]]
then
  cd plugin/src
  # Uncapitalize modules to circumvent a bug of coqdep with mlpack files
  for i in *.ml*
  do
    newi=`echo $i | cut -b 1 | tr '[:upper:]' '[:lower:]'``echo $i | cut -b 2-`;
	tmp="${i}.tmp"
    if [ $i != $newi ]
    then
      echo "Moving " $i "to" $newi;
	  mv $i $tmp;
      mv $tmp $newi;
    fi
  done

  # This file was generated with
  # cat template-coq/_PluginProject | grep "^[^#].*mli\?$" | sed "s/gen-src\///"
  # from MetaCoq root
  files=`cat ../template-coq-files.txt`
  echo "Removing files linked in template-coq:" $files
  rm -f $files
else
  echo "Extraction up to date"
fi
