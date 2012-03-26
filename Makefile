all: opt 

byte:
	ocamlbuild intml.byte

opt:
	ocamlbuild intml.native

tags:
	otags *.ml *.mli

clean:
	rm -rf *.cmo *.cmx *.cmi parser.ml lexer.ml parser.mli _build intml.byte intml.native
