html:
	coqdoc FunctionalProgramming.v
	coqdoc Logic.v
	coqdoc Induction.v

Makefile.coq: Makefile _CoqProject *.v
	coq_makefile -f _CoqProject -o Makefile.coq

clean:
	rm -f *~ *.glob *.vo *.html *.css
