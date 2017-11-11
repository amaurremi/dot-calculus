FILES=Safety.v
OBJECTS=$(FILES:.v=.vo)

TLCDIR=../../lib/tlc/
LIBLN=$(TLCDIR)/LibLN.vo
TLCNAME=TLC

COQINCLUDE=-R $(TLCDIR) $(TLCNAME) -R . \"\"
COQMAKEFILE=$(COQBIN)coq_makefile

PROOFMAKEFILE=Makefile.coq
PROOFS=$(wildcard *.v)

##############
# Main Rules #
##############

.PHONY: all doc proofs clean cleanall
all: proofs #doc

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

doc:
	$(MAKE) -f $(PROOFMAKEFILE) html

%.vo:
	$(MAKE) -f $(PROOFMAKEFILE) $@

all doc clean: $(PROOFMAKEFILE)
%vo: $(PROOFMAKEFILE)

all: $(LIBLN)
doc: $(LIBLN)
proofs: $(LIBLN)
%vo: $(LIBLN)

##############
# Main Rules #
##############

.PHONY: ide _CoqProject
ide: _CoqProject

_CoqProject:
	@echo $(COQINCLUDE) > $@

########################
# Library Dependencies #
########################

$(LIBLN):
	cd $(TLCDIR) && make

###################
# Forced Rebuilds #
###################

.PHONY: $(PROOFMAKEFILE)

$(PROOFMAKEFILE):
	$(COQMAKEFILE) $(COQINCLUDE) -install none -o $(PROOFMAKEFILE) $(PROOFS)
	sed -i -e "s|mkdir -p html|mkdir -p ../doc|g" $(PROOFMAKEFILE)
	sed -i -e "s|-d html|-d ../doc|g" $(PROOFMAKEFILE)
#sed -i -e "s|rm -rf html|rm -rf ../doc|g" $(PROOFMAKEFILE)

graph.png: $(PROOFS)
	coqdep -dumpgraph graph.dot *.v
	dot -Tpng graph.dot > graph.png

#################
# Documentation #
#################

EXTRA_DIR:=../doc/assets
COQDOCFLAGS:= \
  --no-externals \
  --toc --toc-depth 2 --html \
  --index indexpage --no-lib-name --parse-comments \
  --with-header $(EXTRA_DIR)/header.html --with-footer $(EXTRA_DIR)/footer.html
export COQDOCFLAGS
