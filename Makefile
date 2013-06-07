all: 
	ocamlbuild -use-ocamlfind intml.native
	#ocamlbuild -cflags "-g -I +../llvm" -lflags "-g -cc g++ -I +../llvm llvm.cmxa llvm_bitwriter.cmxa" intml.native

byte:
	ocamlbuild -use-ocamlfind intml.byte

opt:
	ocamlbuild -use-ocamlfind intml.native

tags:
	otags *.ml *.mli

clean:
	rm -rf *.cmo *.cmx *.cmi parser.ml lexer.ml parser.mli _build intml.byte intml.native
