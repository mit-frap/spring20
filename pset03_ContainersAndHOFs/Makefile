.PHONY: coq clean

COQC=coqc -q -R ../frap Frap

coq:
	$(COQC) Pset3Sig.v
	$(COQC) Pset3.v
	$(COQC) Pset3Check.v

clean:
	rm -f *.vo *.glob *.aux .lia.cache .nia.cache *.vok *.vos
