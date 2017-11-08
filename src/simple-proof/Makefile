all:
	$(MAKE) -C proof ide
	$(MAKE) -C proof
	$(MAKE) -C proof-ec ide
	$(MAKE) -C proof-ec

clean:
	$(MAKE) -C proof clean
	$(MAKE) -C proof-ec clean

cleanall: clean
	$(MAKE) -C ../../lib/tlc clean
	$(RM) doc/*.html
	$(RM) doc/*.css
