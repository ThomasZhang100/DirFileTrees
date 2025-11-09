#--------------------------------------------------------------------
# Makefile for Assignment 4, Part 3
# Author: 
#--------------------------------------------------------------------

# Macros
#CC = gcc217
CC = gcc217m
CFLAGS =
# CFLAGS = -g
# CFLAGS = -D NDEBUG
# CFLAGS = -D NDEBUG -O

# Dependency rules for non-file targets
all: ft

clean:
	rm -f ftmeminfo*.out

clobber: clean
	rm -f *~ \#*\#

# Dependency Rules
dynarray.o: dynarray.c dynarray.h
	$(CC) $(CFLAGS) -c testsymtable.c

path.o: path.c dynarray.h path.h a4def.h
	$(CC) $(CFLAGS) -c path.c

ft_client.o: ft_client.c ft.h a4def.h
	$(CC) $(CFLAGS) -c ft_client.c

nodeFT.o: nodeFT.c dynarray.h nodeFT.h path.h a4def.h
	$(CC) $(CFLAGS) -c nodeFT.c

ft.o: ft.c dynarray.h nodeFT.h ft.h path.h a4def.h
	$(CC) $(CFLAGS) -c ft.c

ft: ft.o nodeFT.o ft_client.o path.o dynarray.o 
	$(CC) $(CFLAGS) ft.o nodeFT.o ft_client.o path.o dynarray.o -o ft
