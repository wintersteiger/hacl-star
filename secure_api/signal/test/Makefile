FSTAR_HOME=$(HACL_HOME)/../FStar

include $(HACL_HOME)/Makefile.include


FSTAR_INCLUDES += \
	--include $(HACL_HOME)/lib \
	--include $(HACL_HOME)/lib/fst \
	--include $(HACL_HOME)/specs \
	--include $(HACL_HOME)/specs/lemmas \
	--expose_interfaces

LIBS = Lib.IntTypes.fst Lib.RawIntTypes.fst Lib.NatMod.fst Lib.LoopCombinators.fst Lib.Sequence.fst Lib.ByteSequence.fst
LIBS_FILES= $(addprefix $(HACL_HOME)/lib/fst/, $(LIBS))
LIBS_ML = Lib_IntTypes.ml Lib_RawIntTypes.ml Lib_NatMod.ml Lib_LoopCombinators.ml Lib_Sequence.ml Lib_ByteSequence.ml
EXTRACT_MODULES_LIBS = $(addprefix --extract_module , $(LIBS:.fst=))


HACL = Spec.SHA2.fst Spec.Hash.fst Spec.HMAC.fst Spec.HKDF.fst Spec.Curve25519.fst Spec.Ed25519.fst Spec.AES256.fst Spec.AES256_CBC.fst
HACL_FILES= $(addprefix $(HACL_HOME)/specs/, $(HACL))
HACL_ML = Spec_SHA2.ml Spec_Hash.ml Spec_HMAC.ml Spec_HKDF.ml Spec_Curve25519.ml Spec_Ed25519.ml Spec_AES256.ml Spec_AES256_CBC.ml
EXTRACT_MODULES_HACL = $(addprefix --extract_module , $(HACL:.fst=))


SIGNAL = Spec.Signal.Crypto.fst Spec.Signal.Messages.fst Spec.Signal.Core.fst
SIGNAL_FILES= $(addprefix ../, $(SIGNAL))
SIGNAL_ML = Spec_Signal_Crypto.ml Spec_Signal_Messages.ml Spec_Signal_Core.ml
EXTRACT_MODULES_SIGNAL = $(addprefix --extract_module , $(SIGNAL:.fst=))


ML_FILES = $(addprefix signal-ml/, $(LIBS_ML) $(HACL_ML) $(SIGNAL_ML))

#
# Main targets
#

.PHONY=all test

all: test

test: signal.exe

clean:
	rm -rf *.cmi *.cmo *.cmx *.o *~ *.out *.exe *-ml

#
# Primitive targets
#

signal.exe: $(LIBS_FILES) $(HACL_FILES) $(SIGNAL_FILES) Test.Spec.Signal.fst
	mkdir -p signal-ml
	$(FSTAR) --codegen OCaml --lax $(EXTRACT_MODULES_LIBS) $(EXTRACT_MODULES_HACL) $(EXTRACT_MODULES_SIGNAL) --extract_module Test.Spec.Signal --odir signal-ml $^
	@echo 'let _ = test()' >> signal-ml/Test_Spec_Signal.ml
	$(OCAMLOPT) -I signal-ml -I $(HACL_HOME)/lib/ml $(ML_FILES) signal-ml/Test_Spec_Signal.ml -o signal.exe
	./signal.exe
