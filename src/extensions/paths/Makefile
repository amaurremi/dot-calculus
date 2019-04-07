FILES=Safety.v ListExample.v CompilerExample.v SingletonTypeExample.v
OBJECTS=$(FILES:.v=.vo)

COQMAKEFILE=$(COQBIN)coq_makefile

PROOFMAKEFILE=Makefile.coq
PROOFS=$(wildcard *.v)

##############
# Main Rules #
##############

.PHONY: all proofs clean cleanall
all: proofs

proofs: $(PROOFMAKEFILE)
	$(MAKE) -f $(PROOFMAKEFILE) $(OBJECTS)

clean: $(PROOFMAKEFILE)
	$(MAKE) -f $(PROOFMAKEFILE) cleanall

cleanall:: clean
cleanall::
	-rm .*.aux
	-rm *.vo
	-rm *.glob
	-rm *.v.d
	-rm $(PROOFMAKEFILE)

%.vo:
	$(MAKE) -f $(PROOFMAKEFILE) $@

all clean: $(PROOFMAKEFILE)
%vo: $(PROOFMAKEFILE)

#############
# IDE Setup #
#############

########################
# Library Dependencies #
########################

###################
# Forced Rebuilds #
###################

.PHONY: $(PROOFMAKEFILE)

$(PROOFMAKEFILE):
	$(COQMAKEFILE) $(COQINCLUDE) -install none -o $(PROOFMAKEFILE) $(PROOFS)

cleanall::
	-rm *.dot
	-rm *.dpd
