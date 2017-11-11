FILES=Safety.v
OBJECTS=$(FILES:.v=.vo)

PROOFS= \
    Definitions.v \
    Wellformed_store.v \
    Weakening.v \
    Some_lemmas.v \
    Precise_flow.v \
    Has_member.v \
    Inert_types.v \
    Invertible_typing.v \
    Tight_bound_completeness.v \
    Substitution.v \
    Narrowing.v \
    General_to_tight.v \
    Extra_rec.v \
    Canonical_forms1.v \
    Canonical_forms2.v \
    Renaming.v \
    Misc.v \
    Safety.v
PROOFOBJECTS=$(PROOFS:.v=.vo)

TLCDIR=../../lib/tlc/
LIBLN=$(TLCDIR)/LibLN.vo
TLCNAME=TLC

COQINCLUDE=-R $(TLCDIR) $(TLCNAME) -R . \"\"
COQMAKEFILE=$(COQBIN)coq_makefile

PROOFMAKEFILE=Makefile.coq

##############
# Main Rules #
##############

.PHONY: all clean
all:
	$(MAKE) -f $(PROOFMAKEFILE) $(OBJECTS)

clean:
	$(MAKE) -f $(PROOFMAKEFILE) cleanall

%.vo:
	$(MAKE) -f $(PROOFMAKEFILE) $@

all clean: $(PROOFMAKEFILE)
%vo: $(PROOFMAKEFILE)

all: $(LIBLN)
%vo: $(LIBLN)

##############
# Main Rules #
##############

.PHONY: ide
ide: _CoqProject

########################
# Library Dependencies #
########################

$(LIBLN):
	cd $(TLCDIR) && make

###################
# Forced Rebuilds #
###################

.PHONY: init
init: $(PROOFMAKEFILE) _CoqProject

$(PROOFMAKEFILE): .FORCE
	@$(COQMAKEFILE) $(COQINCLUDE) -install none $(PROOFS) > $@

_CoqProject: .FORCE
	@echo $(COQINCLUDE) > $@

.FORCE:
