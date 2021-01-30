.PHONY: coq clean

COQC=coqc -q -R ../../frap Frap

coq: frap
	$(COQC) Pset5aSig.v
	$(COQC) Pset5a.v
	$(COQC) Pset5aCheck.v

frap:
	make -C../../frap

clean:
	rm -f *.vo *.glob *~
