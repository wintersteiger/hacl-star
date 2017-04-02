FSTAR_HOME?=../../../../FStar
KREMLIN_HOME?=$(FSTAR_HOME)/../kremlin
HACL_HOME?=../../..
include ../../Makefile.include

SPECS=$(HACL_HOME)/specs

INCLUDE_DIRS=$(HACL_HOME)/code/lib/kremlin $(SPECS)

GCM_SPECIFIC= \
	Hacl.Impl.GF128.fst \
	Hacl.Spec.GMAC.fst \
	Hacl.Standalone.GMAC.fst


SLOW=

TODO=

GCM_FILES= $(GCM_SPECIFIC)

FSTARB=$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack \
	$(addprefix --include , $(INCLUDE_DIRS)) --include $(KREMLIN_HOME)/kremlib

FSTAR_CT=$(FSTAR_HOME)/bin/fstar.exe --include $(FSTAR_HOME)/ulib/hyperstack \
		--include ../lib $(addprefix --include , $(SPECS)) \
		--include $(KREMLIN_HOME)/kremlib

# Lax typechecking against the restricted integer interface
%.fst-ct: %.fst
	$(FSTAR_CT) --lax $^

all-ct: $(addsuffix -ct, $(GCM_FILES))

# Full typechecking against the transparent integer interface
%.fst-verify: %.fst
	$(FSTARB) $^ --use_hints --record_hints

all-ver: $(addsuffix -verify, $(GCM_FILES))

# Minimal lax typechecking, pre-requisite to any extraction
%.fst-lax: %.fst
	$(FSTARB) --lax $^

all-lax: $(addsuffix -lax, $(GCM_FILES))

# Hints regeneration
%.fst-hints: %.fst
	$(FSTARB) $^ --use_hints --record_hints

all-hints: $(addsuffix -hints, $(GCM_FILES))

clean:
	rm -rf *.exe *.exe.* *.out *~
