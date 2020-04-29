.PHONY: coq clean

COQC=coqc -q -R ../frap Frap

coq:
	$(COQC) Pset11Sig.v
	$(COQC) Pset11Example.v # slow, feel free to comment out
	$(COQC) Pset11.v
	$(COQC) Pset11Check.v

clean:
	rm -f *.vo *.vok *.vos *.glob
