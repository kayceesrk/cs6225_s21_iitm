.PHONY: coq clean

COQC=coqc -q -R ../../frap Frap

coq: frap
	$(COQC) Pset4aSig.v
	$(COQC) Pset4a.v
	$(COQC) Pset4aCheck.v

frap:
	make -C../../frap

clean:
	rm -f *.vo *.glob
