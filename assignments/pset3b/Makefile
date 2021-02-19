.PHONY: coq clean

COQC=coqc -q -R ../../frap Frap

coq: frap
	$(COQC) Pset3bSig.v
	$(COQC) Pset3b.v
	$(COQC) Pset3bCheck.v

frap:
	make -C../../frap

clean:
	rm -f *.vo* *.glob *~
