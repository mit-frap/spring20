.PHONY: coq clean

COQC=coqc -q -R ../frap Frap

coq:
	$(COQC) Pset1Sig.v
	$(COQC) Pset1.v
	$(COQC) Pset1Check.v
clean:
	rm -f *.vo *.glob *.vok *.vos
