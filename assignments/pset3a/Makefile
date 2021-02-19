.PHONY: coq clean

COQC=coqc -q -R ../../frap Frap

coq: frap
	$(COQC) Pset3aSig.v
	$(COQC) Pset3a.v
	$(COQC) Pset3aCheck.v

frap:
	make -C../../frap

clean:
	rm -f *.vo* *.glob *~
