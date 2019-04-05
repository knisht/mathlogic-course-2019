SOURCES=src/Main.hs src/Grammar.hs src/ParseModule.hs src/Completeness.hs src/DeductionTheorem.hs src/BindingProofs.hs
GEN_SOURCES=src/Lexer.x src/Parser.y
GENERATED=src/Lexer.hs src/Parser.hs
PACKAGE=hw4.zip

rwildcard=$(foreach d,$(wildcard $1*),$(call rwildcard,$d/,$2) $(filter $(subst *,%,$2),$d))

BUILD_FILES=$(call rwildcard, , *.o *.hi *.a)



.PHONY: pack all run clean
.SILENT: run



all: parser

run: 
	./parser

clean: 
	rm -rf src/*.o src/*.hi
	rm -rf $(GENERATED)
	rm -rf $(BUILD_FILES)
	rm -f parser

parser: $(GENERATED) $(SOURCES) 
	ghc --make -dynamic -O3 -i./src:lib -Ilib ./src/Main.hs -o parser

	
$(GENERATED): $(GEN_SOURCES) $(SOURCES)
	alex src/Lexer.x -o src/Lexer.hs
	happy src/Parser.y -o src/Parser.hs
	
pack: $(SOURCES) $(C_SOURCES)
	zip $(PACKAGE) -r Makefile src lib
