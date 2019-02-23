SOURCES=Main.hs ParseExpression.hs
C_SOURCES=lib/fnv.c lib/cbits.c
C_HEADERS=lib/text_cbits.h 
BUILT_C_SOURCES=$(C_SOURCES:%.c=%.o)

HS_AUXILAY=Math/NumberTheory/Logarithms.hs Utils.hs GHC/Integer/Compat.hs GHC/Integer/Logarithms/Compat.hs

rwildcard=$(foreach d,$(wildcard $1*),$(call rwildcard,$d/,$2) $(filter $(subst *,%,$2),$d))

HS_MEGAPARSEC_DIR=Text
HS_MEGAPARSEC_SRC=Char.hs Class.hs Common.hs Error.hs Internal.hs Lexer.hs Pos.hs State.hs Stream.hs
HS_MEGAPARSEC_BETTER=$(call rwildcard, , *.o *.hi *.a)
HS_MEGAPARSEC_FULL=Text/Megaparsec/Megaparsec.hs $(HS_MEGAPARSEC_SRC:%=Text/Megaparsec/%)


.PHONY: all run clean
.SILENT: run

all: parser

run: parser
	./parser

BUILT_C_SOURCES: $(C_SOURCES) 
	gcc -c $(C_SOURCES) -o $(BUILT_C_SOURCES)
	

lib/libhelp.a: $(BUILT_C_SOURCES) $(C_HEADERS)
	ar rcs lib/libhelp.a $(BUILT_C_SOURCES) $(C_HEADERS)


clean: 
	rm $(HS_MEGAPARSEC_BETTER)


parser: $(SOURCES) lib/libhelp.a
	ghc-8.0 --make -dynamic lib/libhelp.a -Ilib -DINTEGER_GMP Main.hs -o parser

