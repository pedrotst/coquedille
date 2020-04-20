#!/usr/bin/env bash

dir='eqind'

files=$(ls)

mkdir -p $dir

for f in $files
do
    if grep -q 'eq_ind' $f; then
	echo "Found eq_ind in $f, quarantine it"
        mv $f $dir
    fi
done
