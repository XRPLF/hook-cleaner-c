all: cleaner
cleaner: cleaner.c
	gcc -g cleaner.c -o cleaner
