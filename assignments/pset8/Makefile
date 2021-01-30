.PHONY: coq clean

COQC=coqc -q -R ../../frap Frap -R . ""

coq:
	$(COQC) Pset8Sig.v
	$(COQC) Pset8.v
	$(COQC) Pset8Check.v

clean:
	rm -f *.vo *.glob *~
