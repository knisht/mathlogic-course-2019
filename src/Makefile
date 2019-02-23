SOURCES=Main.hs ParseExpression.hs
C_SOURCES=lib/fnv.c lib/cbits.c
C_HEADERS=lib/text_cbits.h 
BUILT_C_SOURCES=$(C_SOURCES:%.c=%.o)

OUT_DIR=Math GHC Data Control Text lib

rwildcard=$(foreach d,$(wildcard $1*),$(call rwildcard,$d/,$2) $(filter $(subst *,%,$2),$d))

HS_MEGAPARSEC_BETTER=$(call rwildcard, , *.o *.hi *.a)
HS_MEGAPARSEC_FULL=Text/Megaparsec/Megaparsec.hs $(HS_MEGAPARSEC_SRC:%=Text/Megaparsec/%)

PACKAGE=hw1.zip


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
	rm $(HS_MEGAPARSEC_BETTER) 


parser: lib/libhelp.a
	ghc --make -dynamic lib/libhelp.a -Ilib -DINTEGER_GMP Main.hs -o parser

pack: $(SOURCES) $(C_SOURCES)
	zip $(PACKAGE) -r Makefile  $(SOURCES) $(OUT_DIR) Utils.hs
