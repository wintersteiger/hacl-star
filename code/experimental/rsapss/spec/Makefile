FSTAR_HOME   ?= ../../../../../FStar
KREMLIN_HOME ?= ../../../../../kremlin
HACL_HOME    ?= ../../../..

include $(HACL_HOME)/Makefile.include

CACHE_DIR     = .cache
OUTPUT_DIR    = .output
HINT_DIR      = .hints

FSTAR_INCLUDE_DIRS = \
  $(HACL_KREMLIN) \
  $(KREMLIN_HOME)/kremlib \
  $(HACL_HOME)/specs \
  $(HACL_HOME)/lib \
  $(HACL_HOME)/lib/fst \
  $(HACL_HOME)/lib/c

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

LIBS = Lib.IntTypes.fst Lib.RawIntTypes.fst Lib.Sequence.fst Lib.ByteSequence.fst
LIBS_FILES= $(addprefix $(HACL_HOME)/lib/fst/, $(LIBS))
LIBS_ML = Lib_IntTypes.ml Lib_RawIntTypes.ml Lib_Sequence.ml Lib_ByteSequence.ml
LIBS_EX = --extract_module Lib.IntTypes --extract_module Lib.RawIntTypes --extract_module Lib.Sequence --extract_module Lib.ByteSequence

rsapss.exe: $(LIBS_FILES) $(HACL_HOME)/specs/Spec.SHA2.fst high-level/Spec.Bignum.Basic.fst Spec.Karatsuba.fst Spec.Montgomery.fst Spec.RSA.Exp.fst Spec.RSA.fst Spec.RSA.Test.fst
	mkdir -p rsapss-ml
	$(FSTAR) --expose_interfaces --include high-level --codegen OCaml --lax $(LIBS_EX) --extract_module Spec.SHA2 --extract_module Spec.Bignum.Basic \
	--extract_module Spec.Karatsuba.Lemmas --extract_module Spec.Karatsuba --extract_module Spec.Montgomery --extract_module Spec.RSA.Exp --extract_module Spec.RSA \
	--extract_module Spec.RSA.Test --odir rsapss-ml $^
	@echo 'let _ = test()' >> rsapss-ml/Spec_RSA_Test.ml
	$(OCAMLOPT) -I rsapss-ml $(addprefix rsapss-ml/, $(LIBS_ML)) rsapss-ml/Spec_SHA2.ml rsapss-ml/Spec_Bignum_Basic.ml rsapss-ml/Spec_Karatsuba_Lemmas.ml rsapss-ml/Spec_Karatsuba.ml rsapss-ml/Spec_Montgomery.ml rsapss-ml/Spec_RSA_Exp.ml rsapss-ml/Spec_RSA.ml rsapss-ml/Spec_RSA_Test.ml -o rsapss.exe
	./rsapss.exe

rsapss-ll.exe: $(LIBS_FILES) $(HACL_HOME)/specs/Spec.SHA2.fst low-level/Spec.Convert.fst low-level/Spec.Bignum.Base.fst \
	low-level/Spec.Bignum.Basic.fst Spec.Karatsuba.fst Spec.Montgomery.fst Spec.RSA.Exp.fst Spec.RSA.fst Spec.RSA.Test.fst
	mkdir -p rsapss-ml
	$(FSTAR) --expose_interfaces --include low-level --codegen OCaml --lax $(LIBS_EX) --extract_module Spec.SHA2 --extract_module Spec.Convert \
	--extract_module Spec.Bignum.Base --extract_module Spec.Bignum.Basic --extract_module Spec.Karatsuba.Lemmas --extract_module Spec.Karatsuba \
	--extract_module Spec.Montgomery --extract_module Spec.RSA.Exp --extract_module Spec.RSA --extract_module Spec.RSA.Test --odir rsapss-ml $^
	@echo 'let _ = test()' >> rsapss-ml/Spec_RSA_Test.ml
	$(OCAMLOPT) -I rsapss-ml $(addprefix rsapss-ml/, $(LIBS_ML)) rsapss-ml/Spec_SHA2.ml rsapss-ml/Spec_Convert.ml rsapss-ml/Spec_Bignum_Base.ml rsapss-ml/Spec_Bignum_Basic.ml rsapss-ml/Spec_Karatsuba_Lemmas.ml rsapss-ml/Spec_Karatsuba.ml rsapss-ml/Spec_Montgomery.ml rsapss-ml/Spec_RSA_Exp.ml rsapss-ml/Spec_RSA.ml rsapss-ml/Spec_RSA_Test.ml -o rsapss-ll.exe
	./rsapss-ll.exe

clean:
	rm -rf *.cmi *.cmo *.cmx *.o *~ *.out *.exe rsapss-ml
