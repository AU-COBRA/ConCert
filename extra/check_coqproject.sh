#! /usr/bin/env bash
echo "Lines in _RocqProject not present on disk:"
cat _RocqProject | while read f
do
  if [[ ! $f == -* ]] && [ ! -z "$f" ] && [ ! -f "./$f" ]; then
    echo "$f"
  fi
done

echo ".v files on disk not present in _RocqProject:"
find . -type f -not -path "./_opam/*" -name "*.v" | while read f
do
  found=0
  while read f2
  do
    if [[ ! $f2 == -* ]] && [ ! -z "$f2" ] && [[ "./$f2" -ef "$f" ]]; then
      found=1
    fi
  done < <(cat _RocqProject)
  if [ $found -eq 0 ]; then
    echo "$f"
  fi
done
