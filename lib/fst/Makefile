FSTAR_HOME=$(HACL_HOME)/../FStar

include ../../Makefile.include

FSTAR_INCLUDES+=--include $(HACL_HOME)/lib --include $(HACL_HOME)/lib/fst --include $(HACL_HOME)/specs/lemmas

Lib.Buffer.fst-verify: Lib.Buffer.fst
	$(FSTAR) --cache_checked_modules --expose_interfaces Lib.Sequence.fst Lib.IntTypes.fst $<

Lib.Buffer.fsti-verify: ../Lib.Buffer.fsti
	$(FSTAR) --cache_checked_modules --expose_interfaces Lib.Sequence.fst Lib.IntTypes.fst $<

Lib.Modifies.fst-verify: Lib.Modifies.fst
	$(FSTAR) --cache_checked_modules --expose_interfaces Lib.Sequence.fst Lib.IntTypes.fst Lib.Buffer.fst $<

Lib.BufferOps.fst-verify: Lib.BufferOps.fst
	$(FSTAR) --cache_checked_modules --expose_interfaces Lib.Sequence.fst Lib.IntTypes.fst Lib.Buffer.fst $<
