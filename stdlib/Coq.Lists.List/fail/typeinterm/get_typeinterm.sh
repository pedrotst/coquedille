#!/usr/bin/env bash

dir='typeinterm'

files=$(ls)

mkdir -p $dir

for f in $files
do
    if grep -q 'not implemented' $f; then
	echo "Found tprod in $f, quarantine it"
        mv $f $dir
    fi
done
