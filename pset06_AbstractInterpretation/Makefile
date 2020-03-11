.PHONY: coq clean

COQC=coqc -q -R ../frap Frap

coq:
	$(COQC) Pset6Sig.v
	$(COQC) Pset6.v
	$(COQC) Pset6Check.v

clean:
	rm -f *.vo *.vok *.vos *.glob
