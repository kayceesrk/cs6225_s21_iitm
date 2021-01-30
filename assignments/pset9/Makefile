.PHONY: coq clean

COQC=coqc -q -R ../../frap Frap -R . ""

coq:
	$(COQC) Pset9.v

clean:
	rm -f *.vo *.glob
