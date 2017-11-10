FILES=Safety.v
OBJECTS=$(FILES:.v=.vo)

TLCDIR=../../../lib/tlc
DOCDIR=../doc

TLCSRC=$(TLCDIR)/src
LIBLN=$(TLCSRC)/LibLN.vo
TLCNAME=TLC

COQINCLUDE=-R $(TLCSRC) $(TLCNAME) -R . \"\"
COQMAKEFILE=$(COQBIN)coq_makefile

PROOFMAKEFILE=Makefile.coq
PROOFS=$(wildcard *.v)

##############
# Main Rules #
##############

.PHONY: all doc proofs clean cleanall
all: proofs doc

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

doc: $(DOCDIR)/toc.html

%.vo: %.v
	$(MAKE) -f $(PROOFMAKEFILE) $@

all doc clean: $(PROOFMAKEFILE)
%vo: $(PROOFMAKEFILE)

all: $(LIBLN)
doc: $(LIBLN)
proofs: $(LIBLN)
%vo: $(LIBLN)

#############
# IDE Setup #
#############

.PHONY: ide _CoqProject
ide: _CoqProject

_CoqProject:
	echo $(COQINCLUDE) > _CoqProject

########################
# Library Dependencies #
########################

$(LIBLN): $(wildcard $(TLCSRC)/*.v)
	$(MAKE) -C $(TLCDIR)

###################
# Forced Rebuilds #
###################

.PHONY: $(PROOFMAKEFILE)

$(PROOFMAKEFILE):
	$(COQMAKEFILE) $(COQINCLUDE) -install none -o $(PROOFMAKEFILE) $(PROOFS)
	sed -i -e "s|mkdir -p html|mkdir -p $(DOCDIR)|g" $(PROOFMAKEFILE)
	sed -i -e "s|-d html|-d $(DOCDIR)|g" $(PROOFMAKEFILE)
	sed -i -e "s|rm -rf html|rm -f $(DOCDIR)/*.*|g" $(PROOFMAKEFILE)

#################
# Documentation #
#################

DOCDEP=$(shell coqdep -sort $(FILES) | sed -e "s|\\.vo|\\.v|g")

$(DOCDIR)/toc.html: $(DOCDEP)
	$(MAKE) -f $(PROOFMAKEFILE) VFILES="$(DOCDEP)" html

EXTRA_DIR:=$(DOCDIR)/assets
COQDOCFLAGS:= \
  --no-externals \
  --toc --toc-depth 2 --html \
  --index indexpage --no-lib-name --parse-comments \
  --with-header $(EXTRA_DIR)/header.html --with-footer $(EXTRA_DIR)/footer.html
export COQDOCFLAGS

##########
# Graphs #
##########

GRAPHDEP=$(shell coqdep -sort $(FILES) | sed -e "s|\\.vo|\\.v|g")
GRAPHEXCLUDE=?

graph: $(DOCDIR)/graph.png

graph.dot: $(GRAPHDEP)
	coqdep -dumpgraph graph.dot $(GRAPHDEP) >/dev/null 2>/dev/null

$(DOCDIR)/graph.png: graph.dot $(PROOFS)
	dot -Tpng graph.dot > $(DOCDIR)/graph.png

######################
# Lemma Dependencies #
######################

DPDMODALL=$(shell coqdep -sort Safety.v | sed "s|\(\./\)||g" | sed "s|\.vo||g")
DPDFILENAME=dpdraw.dpd
DPDDOT=$(DPDFILENAME:=.dot)

DPDEXCLUDE ?=
DPDMODULES=$(filter-out $(DPDEXCLUDE), $(DPDMODALL))

DPDTEXT=Require dpdgraph.dpdgraph. Require LibLN. Require Coq.Program.Equality.
DPDTEXT+=Require $(DPDMODULES).
DPDTEXT+=Set DependGraph File \"$(DPDFILENAME)\".
DPDTEXT+=Print FileDependGraph $(DPDMODULES).

$(DPDFILENAME): $(shell coqdep -sort $(FILES)) all
	echo $(DPDTEXT) | coqtop -R $(TLCSRC) $(TLCNAME) -notop

$(DPDDOT): $(DPDFILENAME)
	dpd2dot -without-defs $<
	dpdusage $<

.PHONY: dpdraw $(DPDOT) $(DPDFILENAME)
dpdraw: $(DPDDOT)

DPDFILTER=dpdgraph.dpd
DPDFILDOT=$(DPDFILTER:=.dot)
$(DPDFILDOT): $(DPDFILTER)
	dpd2dot -without-defs $<

$(DPDFILTER): $(DPDFILENAME)
	grep -P '(kind=construct|^N: [0-9]+ "[^"]*(_ind|mutind|_mut)")' $(DPDFILENAME) | sed -e "s|^N: \([0-9][0-9]*\) .*|\1|g" | paste -sd "|" | xargs -I {} grep -P -v "^((E: ({}) )|(E: [0-9]+ ({}) )|(N: ({}) ))" $(DPDFILENAME) > $(DPDFILTER)

.PHONY: dpdgraph $(DPDFILDOT) $(DPDFILTER)
dpdgraph: $(DPDFILDOT)

cleanall::
	-rm *.dot
	-rm *.dpd
