SOURCES=Main.hs ParseExpression.hs
C_SOURCES=lib/fnv.c lib/cbits.c
C_HEADERS=lib/text_cbits.h 
BUILT_C_SOURCES=$(C_SOURCES:%.c=%.o)


.PHONY: all run
.SILENT: run

all: parser

run: parser
	./parser

BUILT_C_SOURCES: $(C_SOURCES) 
	gcc -c $(C_SOURCES) -o $(BUILT_C_SOURCES)
	

lib/libhelp.a: $(BUILT_C_SOURCES) $(C_HEADERS)
	ar rcs lib/libhelp.a $(BUILT_C_SOURCES) $(C_HEADERS)


parser: $(SOURCES) lib/libhelp.a
	ghc-8.0 --make -dynamic lib/libhelp.a -Ilib -DINTEGER_GMP Main.hs -o parser

