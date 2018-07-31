#!/bin/bash

#cancel loop with ^C, cancel one iteration with ^\

while read
do
	clear
	if ./a.out "$@"
	then
		echo -e "\e[42m \e[0m"  #green
	else
		echo -e "\e[41m \e[0m"  #red
	fi
done
