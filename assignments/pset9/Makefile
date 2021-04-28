.PHONY: coq clean

COQC=coqc -q -R ../../frap Frap -R . ""

coq:
	$(COQC) Pset9Sig
	$(COQC) Pset9
	$(COQC) Pset9Check

clean:
	rm -f *.vo* *.glob
