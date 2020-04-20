#!/usr/bin/env bash

files=$(ls)

mkdir -p In

for f in $files
do
    if grep -q 'In' $f; then
	echo "Found In in $f, quarantine it"
        mv $f In
    fi
done
