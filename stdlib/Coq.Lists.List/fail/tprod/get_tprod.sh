#!/usr/bin/env bash

files=$(ls)

mkdir -p tprod

for f in $files
do
    if grep -q 'tprodT' $f; then
	echo "Found tprod in $f, quarantine it"
        mv $f tprod
    fi
done
