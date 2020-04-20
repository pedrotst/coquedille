#!/usr/bin/env bash

dir='eqtsort'

files=$(ls)

mkdir -p $dir

for f in $files
do
    if grep -q 'eq tSort' $f; then
	echo "Found tprod in $f, quarantine it"
        mv $f $dir
    fi
done
