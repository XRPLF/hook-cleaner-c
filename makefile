all: hook-cleaner
hook-cleaner: cleaner.c
	gcc -g cleaner.c -o hook-cleaner
install: hook-cleaner
	cp hook-cleaner /usr/bin/
