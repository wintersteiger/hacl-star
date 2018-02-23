include ../../../Makefile.include

# Verify everything with the used parameters
BIGNUM= \
	Hacl.Bignum.Fdifference.fst \
	Hacl.Bignum.Fmul.fst \
	Hacl.Bignum.Fproduct.fst \
	Hacl.Bignum.Fscalar.fst \
	Hacl.Bignum.Fsum.fst \
	Hacl.Bignum.Limb.fst \
	Hacl.Bignum.Wide.fst \
	Hacl.Bignum.fst \
	specs/Hacl.Spec.Bignum.Bigint.fst \
	specs/Hacl.Spec.Bignum.Fdifference.fst \
	specs/Hacl.Spec.Bignum.Field.fst \
	specs/Hacl.Spec.Bignum.Fmul.fst \
	specs/Hacl.Spec.Bignum.Fproduct.fst \
	specs/Hacl.Spec.Bignum.Fscalar.fst \
	specs/Hacl.Spec.Bignum.Fsum.fst \
	specs/Hacl.Spec.Bignum.fst

X25519_SPECIFIC= \
	specs/Hacl.Spec.Curve25519.Lemmas.fst \
	Hacl.Bignum.Parameters.fst \
	specs/Hacl.Spec.Bignum.Modulo.fst \
	specs/Hacl.Spec.EC.AddAndDouble.fst \
	specs/Hacl.Spec.Bignum.Fsquare.fst \
	specs/Hacl.Spec.Bignum.Crecip.fst \
	Hacl.Bignum.Modulo.fst \
	Hacl.Bignum.Fsquare.fst \
	Hacl.Bignum.Crecip.fst \
	specs/Hacl.Spec.EC.Point.fst \
	Hacl.EC.Point.fst \
	specs/Hacl.Spec.EC.AddAndDouble2.fst \
	specs/Hacl.Spec.EC.AddAndDouble3.fst \
	specs/Hacl.Spec.EC.Format.Lemmas.fst \
	specs/Hacl.Spec.EC.Format.fst \
	Hacl.EC.Format.fst \
	Hacl.EC.AddAndDouble.fst \
	specs/Hacl.Spec.EC.Ladder.Lemmas.fst \
	specs/Hacl.Spec.EC.Ladder.fst \
	Hacl.EC.Ladder.SmallLoop.fst \
	Hacl.EC.Ladder.BigLoop.fst \
	Hacl.EC.Ladder.fst \
	specs/Hacl.Spec.EC.fst \
	Hacl.EC.fst \
	Hacl.Curve25519.fst

# Files that are too slow and for which verification speed must improve
SLOW=

FSTAR_INCLUDES+=--include specs
X25519_FILES=$(BIGNUM) $(X25519_SPECIFIC)

# Parameters for interactive mode
%.fst-in:
	@echo $(OPTIONS) --hint_info \
	$(FSTAR_INCLUDES)

ct: $(addsuffix -lax, $(X25519_FILES))
	# Using the --verify_all argument to lift abstractions, typechecks all dependencies of Curve25519.fst
	$(FSTAR) --lax --verify_all Hacl.Curve25519.fst

bignum-ver: $(addsuffix -reloc-verify, $(BIGNUM))
specific-ver: $(addsuffix -verify, $(X25519_SPECIFIC))
verify: bignum-ver specific-ver
all-ver: verify
all-ct: ct

# Hints regeneration
bignum-hints: $(addsuffix .reloc.hints, $(BIGNUM))
specific-hints: $(addsuffix .hints, $(X25519_SPECIFIC))
hints: bignum-hints specific-hints
all-hints: hints

# For CI, all modules restricted from incomplete or slow ones
bignum-ci: $(addsuffix -reloc-verify, $(filter-out $(SLOW), $(BIGNUM)))
specific-ci: $(addsuffix -verify, $(filter-out $(SLOW), $(X25519_SPECIFIC)))
all-ci: bignum-ci specific-ci


CFLAGS=-Wall -Wextra -Wno-unused-parameter -Wno-unused-variable
KREMLIN_ARGS+= -I specs/ -tmpdir x25519-c \
	-drop Spec.*,Hacl.Spec.*,Hacl.Cast,Hacl.UInt.*,Hacl.Endianness,Hacl.UInt8,Hacl.UInt16,Hacl.UInt32,Hacl.UInt64,Hacl.UInt128,Prims \
	$(KREMLIN_TESTLIB)

# Acknowledge the F* dependency graph
.PHONY: depend
depend:
	$(FSTAR) --dep make $(X25519_FILES) > .depend
-include .depend

x25519-c/out.krml: $(X25519_FILES) Hacl.Test.X25519.fst
	$(KREMLIN) $(KREMLIN_ARGS) -skip-translation $^ -o $@

x25519-c/Hacl_Curve25519.c x25519-c/Hacl_Test_X25519.c: x25519-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -no-prefix Hacl.Test.X25519 \
	 	-bundle 'Hacl.Curve25519=Hacl.Bignum,Hacl.Bignum.*,Hacl.EC,Hacl.EC.*' \
		-skip-compilation $^ -o $@

x25519.exe: x25519-c/out.krml
	$(KREMLIN) $(KREMLIN_ARGS) -no-prefix Hacl.Test.X25519 \
	 	-bundle 'Hacl.Curve25519=Hacl.Bignum,Hacl.Bignum.*,Hacl.EC,Hacl.EC.*' \
		$^ -o $@
	./$@

extract-c: x25519-c/Hacl_Curve25519.c x25519-c/Hacl_Test_X25519.c

test: x25519.exe

CC=gcc-7 -Ofast -flto -march=native -mtune=native

test-curve25519.exe:
	$(CC) -c $(KREMLIN_HOME)/kremlib/testlib.c -o testlib.o -I$(KREMLIN_HOME)/kremlib
	$(CC) -c $(KREMLIN_HOME)/kremlib/kremlib.c -o kremlib.o -I$(KREMLIN_HOME)/kremlib
	$(CC) -c x25519-c/Hacl_Curve25519.c -o Hacl_Curve25519.o -I$(KREMLIN_HOME)/kremlib
	$(CC) -c x25519-c/Hacl_Test_X25519.c -o Hacl_Test_X25519.o -I$(KREMLIN_HOME)/kremlib
	$(CC) -o test-curve25519.exe kremlib.o testlib.o Hacl_Curve25519.o Hacl_Test_X25519.o -I/opt/kremlin/kremlib
	./test-curve25519.exe

X25519_LIB= \
	Hacl.Bignum.Parameters.fst \
	Hacl.Spec.Bignum.Modulo.fst \
	Hacl.Spec.EC.AddAndDouble.fst \
	Hacl.Spec.Bignum.Fsquare.fst \
	Hacl.Spec.Bignum.Crecip.fst \
	Hacl.Bignum.Modulo.fst \
	Hacl.Bignum.Fsquare.fst \
	Hacl.Bignum.Crecip.fst \
	Hacl.EC.Point.fst \
	Hacl.Spec.EC.Format.Lemmas.fst \
	Hacl.Spec.EC.Format.fst \
	Hacl.EC.Format.fst \


X25519_ONLY=Hacl.Spec.EC.Point.fst \
	Hacl.Spec.Curve25519.Lemmas.fst \
	Hacl.Spec.EC.AddAndDouble2.fst \
	Hacl.EC.AddAndDouble.fst \
	Hacl.Spec.EC.Ladder.Lemmas.fst \
	Hacl.Spec.EC.Ladder.fst \
	Hacl.EC.Ladder.SmallLoop.fst \
	Hacl.EC.Ladder.BigLoop.fst \
	Hacl.EC.Ladder.fst \
	Hacl.Spec.EC.fst \
	Hacl.EC.fst

count-line:
	@echo "X25519 LIB LOC"
	cloc --force-lang=ocaml $(X25519_LIB)
	@echo "X25519 ONLY LOC"
	cloc --force-lang=ocaml $(X25519_ONLY)

clean:
	rm -rf *.exe *.exe.* *.out *~ x25519-c
