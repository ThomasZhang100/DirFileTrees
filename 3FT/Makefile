#--------------------------------------------------------------------
# Makefile for Assignment 4, Part 2
# dt* targets are built using checkerDT
# rules to build dtBad*.o and nodeBad*.o from source will fail
# Author: Christopher Moretti
#--------------------------------------------------------------------

GCC = gcc217
#GCC = gcc217m

all: ft

clean:
	rm -f ftmeminfo*.out

clobber: clean
	rm -f ft.o  *~

# Dependency Rules
dynarray.o: dynarray.c dynarray.h
	$(GCC) -g -c $<

path.o: path.c dynarray.h path.h a4def.h
	$(GCC) -g -c $<

ft_client.o: ft_client.c ft.h a4def.h
	$(GCC) -g -c $<

nodeFT.o: nodeFT.c dynarray.h nodeFT.h path.h a4def.h
	$(GCC) -g -c $<

ft.o: ft.c dynarray.h nodeDT.h dt.h path.h a4def.h
	$(GCC) -g -c $<

ft: ft.o nodeFT.o ft_client.o path.o dynarray.o 
	$(GCC) -g -c $< ft.o nodeFT.o ft_client.o path.o dynarray.o -o ft
