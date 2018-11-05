CC=gcc
CFLAGS=-g -Wall -Wno-misleading-indentation

all: lisp
	./lisp

lisp: lisp.o
