FSTAR_HOME   ?= ../../../../../../FStar
KREMLIN_HOME ?= ../../../../../../kremlin
HACL_HOME    ?= ../../../../..

CACHE_DIR     = .cache
OUTPUT_DIR    = .output
HINT_DIR      = .hints

FSTAR_INCLUDE_DIRS = \
  $(HACL_KREMLIN) \
  $(KREMLIN_HOME)/kremlib \
  $(HACL_HOME)/specs \
  $(HACL_HOME)/lib \
  $(HACL_HOME)/lib/fst \
  $(HACL_HOME)/lib/c \
  $(HACL_HOME)/code/experimental/rsapss/spec

FSTAR_INCLUDES = $(addprefix --include ,$(FSTAR_INCLUDE_DIRS))

FSTAR = $(FSTAR_HOME)/bin/fstar.exe $(OTHERFLAGS) \
  --cache_checked_modules --cache_dir $(CACHE_DIR) \
  --odir $(OUTPUT_DIR) $(FSTAR_INCLUDES)

FSTARR = $(FSTAR_HOME)/bin/fstar.exe $(OTHERFLAGS) \
  --cache_dir $(CACHE_DIR) \
  --odir $(OUTPUT_DIR) $(FSTAR_INCLUDES)

ENABLE_HINTS = --use_hints --use_hint_hashes --record_hints --query_stats

%.fst-in:
	@echo --cache_checked_modules --cache_dir $(CACHE_DIR) \
	$(FSTAR_INCLUDES) \
	$(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(basename $@).fst.hints

%.fsti-in:
	@echo --cache_checked_modules --cache_dir $(CACHE_DIR) \
	$(FSTAR_INCLUDES) \
	$(ENABLE_HINTS) --hint_file $(HINT_DIR)/$(basename $@).fsti.hints
