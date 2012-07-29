all: 
	ocamlbuild -cflags "-g -I +llvm-3.0" -lflags "-g -cc g++ -I +llvm-3.0 llvm.cma llvm_bitwriter.cma" intml.byte

byte:
	ocamlbuild intml.byte

opt:
	ocamlbuild intml.native

tags:
	otags *.ml *.mli

clean:
	rm -rf *.cmo *.cmx *.cmi parser.ml lexer.ml parser.mli _build intml.byte intml.native
