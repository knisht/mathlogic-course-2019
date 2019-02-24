SOURCES=src/Main.hs src/LogicParser.hs src/Minimize.hs
C_SOURCES=lib/fnv.c lib/cbits.c
C_HEADERS=lib/text_cbits.h 
BUILT_C_SOURCES=$(C_SOURCES:%.c=%.o)

PACK=lib src

rwildcard=$(foreach d,$(wildcard $1*),$(call rwildcard,$d/,$2) $(filter $(subst *,%,$2),$d))

BUILD_FILES=$(call rwildcard, , *.o *.hi *.a)

PACKAGE=hw2.zip


.PHONY: pack all run clean
.SILENT: run

all: parser

run: 
	./parser

lib/libhelp.a: 
	gcc -c lib/fnv.c -o lib/fnv.o
	gcc -c lib/cbits.c -o lib/cbits.o
	ar rcs lib/libhelp.a lib/fnv.o lib/cbits.o lib/text_cbits.h

clean: 
	rm $(BUILD_FILES) 


parser: lib/libhelp.a
	ghc-8.0 --make -dynamic lib/libhelp.a -isrc:lib -Ilib -DINTEGER_GMP src/Main.hs -o parser

pack: $(SOURCES) $(C_SOURCES)
	zip $(PACKAGE) -r Makefile  $(PACK)
