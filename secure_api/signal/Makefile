# include $(HACL_HOME)/Makefile.include

# Can be relocated to HACL's Makefile.include
HACL_CODE	= $(HACL_HOME)/code
HACL_SPECS	= $(HACL_HOME)/specs

HACL_LIBS = \
	$(HACL_HOME)/lib/fst/Lib.IntTypes.fst \
	$(HACL_HOME)/lib/fst/Lib.RawIntTypes.fst \
	$(HACL_HOME)/lib/fst/Lib.Buffer.fst \
	$(HACL_HOME)/lib/fst/Lib.ByteBuffer.fst \
	$(HACL_HOME)/lib/fst/Lib.LoopCombinators.fst \
	$(HACL_HOME)/lib/fst/Lib.Sequence.fst \
	$(HACL_HOME)/lib/fst/Lib.ByteSequence.fst \
	$(HACL_HOME)/lib/fst/Lib.Loops.fst

CRYPTO = \
	$(HACL_HOME)/code/signal/curve25519/Hacl.Curve25519_51.fst \
	$(HACL_HOME)/code/signal/curve25519/Hacl.Impl.Curve25519.Generic.fst


# Local F* includes
INCLUDE_DIRS = \
	$(KREMLIN_HOME)/kremlib \
	$(HACL_HOME)/lib

FSTAR_INCLUDES = $(addprefix --include ,$(INCLUDE_DIRS))

# Local FStar invocation
FSTAR	= $(FSTAR_HOME)/bin/fstar.exe \
  --cache_checked_modules \
  --use_two_phase_tc true \
  --cache_dir $(CACHE_DIR) --odir $(OUTPUT_DIR) \
  $(FSTAR_INCLUDES) \
  --use_hints # --record_hints --hint_info

# Local Kremlin arguments for extraction
KREMLIN_ARGS += -verbose \
	-no-prefix C.Loops \
	-bundle "Prims,Lib.*,FStar,FStar.*,LowStar,C.Loops,C.Loops.Spec.Loops,C.Compat,C.Compat.*[rename=Kremlin]" \
	-bundle "Hacl.Curve25519_51=Hacl.Impl.Curve25519.*,Hacl.Spec.Curve25519.*,C,C.*" \
	-bundle "Impl.Signal.Core=Impl.Signal.*" \
	-bundle "*[rename=Misc]" \
	-d reachability \
	-ccopt -march=native

BASE_OBJ = ../../lib/c/Spec_Lib_Print.o $(KREMLIN_HOME)/kremlib/testlib.o $(KREMLIN_HOME)/kremlib/kremlib.o $(KREMLIN_HOME)/kremlib/kremstr.o

KREMLIN = $(KREMLIN_HOME)/krml

c-signal/out.krml: $(HACL_LIBS) $(wildcard *.fst) $(wildcard *.fsti)
	mkdir -p c-signal
	$(KREMLIN) -I $(HACL_HOME)/specs -I $(HACL_HOME)/specs/lemmas -I . \
	  -I $(HACL_HOME)/code/signal/curve25519 \
	  -tmpdir c-signal \
	  -I $(HACL_HOME)/specs -I $(HACL_HOME)/lib \
	  -skip-translation $(HACL_LIBS) $(CRYPTO) Impl.Signal.Core.fst Impl.Signal.Crypto.fst

c-signal/Impl_Signal_Core.c: c-signal/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -fparentheses -tmpdir c-signal -skip-compilation \
	$^ -o $@


extract-c: c-signal/Impl_Signal_Core.c

define WASM_EXPORTED_FUNCTIONS
"_Signal_Impl_Core_verifySig", \
"_Signal_Impl_Core_calculate_sending_ratchet", \
"_Signal_Impl_Core_init_session_initiator", \
"_Signal_Impl_Core_init_session_responder", \
"_Signal_Impl_Core_fill_message_keys", \
"_Signal_Impl_Core_encrypt", \
"_Signal_Impl_Core_add_mac", \
"_Signal_Impl_Core_build_mac_input", \
"_Signal_Impl_Core_verify_mac_and_decrypt", \
"_Signal_Impl_Core_generate_key_pair", \
"_Signal_Impl_Core_generate_registration_id", \
"_Signal_Impl_Core_generate_signed_pre_key", \
"_malloc", "_free"
endef

signal-wasm/Signal_Impl_Core.wasm: c-signal/out.krml
	$(KREMLIN) $(KOPTS) $^ -tmpdir c-signal -wasm \
	-bundle "Impl.Signal.Core=Prims,Lib.*,FStar,FStar.*,LowStar,C.Loops,C.Loops.Spec.Loops,Hacl.Spec.Endianness,Hacl.Endianness,Seq.Create,Spec.*,LowStar.*,Impl.Signal.*" \
	-minimal -d wasm

extract-wasm: signal-wasm/Signal_Impl_Core.wasm

.PHONY:test-open

test-vanilla:
	sed \
		-e 's|{{{PLACEHOLDER}}}|<script type="text/javascript" src="../src/FStarCore.js" data-cover-never></script>|' \
	  ../test/index.html.proto \
		 > ../test/index.html && \
	http-server ..

test-fstar: signal-wasm/Signal_Impl_Core.wasm
	sed -e 's|{{{PLACEHOLDER}}}| \
	  <script type="text/javascript" src="../fstar/signal-wasm/shell.js" data-cover-never></script> \
	  <script type="text/javascript" src="../fstar/signal-wasm/externals.js" data-cover-never></script> \
	  <script type="text/javascript" src="../fstar/signal-wasm/loader.js" data-cover-never></script> \
	  <script type="text/javascript" src="../fstar/signal-wasm/browser.js" data-cover-never></script> \
	  <script type="text/javascript" src="../fstar/signal-wasm/FStarCore.js" data-cover-never></script>|' \
	  ../test/index.html.proto \
		 > ../test/index.html && \
	http-server ..

test-sanity: signal-wasm/Signal_Impl_Core.wasm
	# This target checks that the modules can be linked together... and that
	# we reach the point where we're ready to run a (non-existent) main
	cd signal-wasm && node main.js | grep "... error running main"

all: extract-c

clean:
	rm -rf *~ *.krml c-signal/ *.checked *.checked.lax
