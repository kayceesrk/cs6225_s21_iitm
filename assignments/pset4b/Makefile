.PHONY: coq clean

COQC=coqc -q -R ../../frap Frap

coq: frap
	$(COQC) Pset4bSig.v
	$(COQC) Pset4b.v
	$(COQC) Pset4bCheck.v

frap:
	make -C../../frap

clean:
	rm -f *.vo *.glob
