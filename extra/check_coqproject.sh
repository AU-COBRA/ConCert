#! /usr/bin/env bash
echo "Lines in _CoqProject not present on disk:"
cat _CoqProject | while read f
do
  if [[ ! $f == -* ]] && [ ! -z "$f" ] && [ ! -f "./$f" ]; then
    echo "$f"
  fi
done

echo ".v files on disk not present in _CoqProject:"
find . -type f -not -path "./_opam/*" -name "*.v" | while read f
do
  found=0
  while read f2
  do
    if [[ ! $f2 == -* ]] && [ ! -z "$f2" ] && [[ "./$f2" -ef "$f" ]]; then
      found=1
    fi
  done < <(cat _CoqProject)
  if [ $found -eq 0 ]; then
    echo "$f"
  fi
done
