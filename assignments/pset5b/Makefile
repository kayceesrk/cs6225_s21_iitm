.PHONY: coq clean

COQC=coqc -q -R ../../frap Frap

coq: frap
	$(COQC) Pset5bSig.v
	$(COQC) Pset5b.v
	$(COQC) Pset5bCheck.v

frap:
	make -C../../frap

clean:
	rm -f *.vo *.glob *~
