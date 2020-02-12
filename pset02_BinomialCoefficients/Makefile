.PHONY: coq clean

COQC=coqc -q -R ../frap Frap

coq:
	$(COQC) Pset2Sig.v
	$(COQC) Pset2.v
	$(COQC) Pset2Check.v

clean:
	rm -f *.vo *.glob *.aux .lia.cache .nia.cache *.vok *.vos
