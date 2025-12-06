SOURCES = syntax.ml parser.mly lexer.mll env.ml value.ml eval.ml main.ml
RESULT = interpreter
OCAMLMAKEFILE = ~/include/OCamlMakefile
include $(OCAMLMAKEFILE)

test : bc
	../test-suite/check-vm ./interpreter 0 1 2 3 4
	$(MAKE) clean
