#!/bin/bash

if ! which inotifywait &>/dev/null
then
	echo This script needs inotifywait. 1>&2
	exit 1
fi

dir="${1:-.}"
echo Running in \"$PWD\".
echo Watching C files in \""$(readlink -f "$dir")"\".

inotifywait -q -m -r -e CLOSE_WRITE --format %f "$dir" |
while read f
do
	if [[ "$f" == *.[ch] ]]
	then
		clear
		#echo COMPILING...
		#echo

		if clang -ansi \
			-Weverything \
			-Wno-missing-prototypes \
			-Wno-missing-variable-declarations \
			-Wno-switch-enum \
			-Wno-padded \
			-pedantic-errors \
			-march=native \
			-fno-strict-aliasing \
			"$dir/main.c"
		then
			#echo
			echo COMPILATION SUCCESSFUL.
		fi
	fi
done
