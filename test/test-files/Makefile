OPENSSL_LIB=$(HACL_HOME)/other_providers/openssl
OPENSSL_INCLUDE=$(HACL_HOME)/other_providers/openssl/include

.PHONY=build

CC=gcc-7 -O3 -march=native -mtune=native -funroll-loops
#CC=gcc-7 -S -Ofast -flto -march=native -mtune=native
#CC=gcc-7 -pg
#CFLAGS=-Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops -flto

INCLUDE_C=-I $(HACL_HOME)/code/lib/kremlin -I $(HACL_HOME)/specs -I $(KREMLIN_HOME)/kremlib -I $(KREMLIN_HOME)/include -I $(HACL_HOME)/snapshots/hacl-c/

CC := $(CC) $(INCLUDE_C)

test-rsapss.exe:
	$(CC) $(CFLAGS) -c $(KREMLIN_HOME)/kremlib/testlib.c -o testlib.o
	$(CC) $(CFLAGS) -c $(HACL_HOME)/snapshots/hacl-c/Hacl_Unverified_Random.c -o Hacl_Unverified_Random.o
	$(CC) $(CFLAGS) -c $(HACL_HOME)/snapshots/hacl-c/Hacl_SHA2_256.c -o Hacl_SHA2_256.o
	$(CC) $(CFLAGS) -c $(HACL_HOME)/snapshots/hacl-c/Hacl_RSAPSS.c -o Hacl_RSAPSS.o
	$(CC) $(CFLAGS) -c Hacl_Perf_RSA.c -o Hacl_Perf_RSA.o -L$(OPENSSL_LIB) -I$(OPENSSL_INCLUDE)
	$(CC) $(CFLAGS) -o test-rsapss.exe testlib.o Hacl_Unverified_Random.o Hacl_SHA2_256.o Hacl_RSAPSS.o Hacl_Perf_RSA.o -L$(OPENSSL_LIB) -I$(OPENSSL_INCLUDE) -lcrypto

test-unit-rsapss: test-rsapss.exe
	./test-rsapss.exe unit-test

test-perf-rsapss: test-rsapss.exe
	./test-rsapss.exe perf

test-mult.exe:
	$(CC) $(CFLAGS) -c $(KREMLIN_HOME)/kremlib/testlib.c -o testlib.o
	$(CC) $(CFLAGS) -c Hacl_Mult.c -o Hacl_Mult.o
	$(CC) $(CFLAGS) -c $(HACL_HOME)/snapshots/hacl-c/Hacl_Unverified_Random.c -o Hacl_Unverified_Random.o
	$(CC) $(CFLAGS) -c Hacl_Perf_Mult.c -o Hacl_Perf_Mult.o
	$(CC) $(CFLAGS) -o test-mult.exe testlib.o Hacl_Unverified_Random.o Hacl_Mult.o Hacl_Perf_Mult.o -L$(OPENSSL_LIB) -I$(OPENSSL_INCLUDE) -lcrypto

test-mult: test-mult.exe
	./test-mult.exe

test-exp.exe:
	$(CC) $(CFLAGS) -c $(KREMLIN_HOME)/kremlib/testlib.c -o testlib.o -I$(KREMLIN_HOME)/kremlib
	$(CC) $(CFLAGS) -c $(HACL_HOME)/snapshots/hacl-c/Hacl_SHA2_256.c -o Hacl_SHA2_256.o -I$(KREMLIN_HOME)/kremlib -I$(HACL_HOME)/snapshots/hacl-c -I$(HACL_HOME)/snapshots/hacl-c-experimental
	$(CC) $(CFLAGS) -c $(HACL_HOME)/snapshots/hacl-c/Hacl_RSAPSS.c -o Hacl_RSAPSS.o -I$(KREMLIN_HOME)/kremlib -I$(HACL_HOME)/snapshots/hacl-c -I$(HACL_HOME)/snapshots/hacl-c-experimental
	$(CC) $(CFLAGS) -c Hacl_Perf_Exp.c -o Hacl_Perf_Exp.o -L$(OPENSSL_LIB) -I$(OPENSSL_INCLUDE) -I$(KREMLIN_HOME)/kremlib -I$(HACL_HOME)/snapshots/hacl-c -I$(HACL_HOME)/snapshots/hacl-c-experimental
	$(CC) $(CFLAGS) -o test-exp.exe  testlib.o Hacl_SHA2_256.o Hacl_RSAPSS.o  Hacl_Perf_Exp.o -lcrypto -L$(HACL_HOME)/build-experimental -L$(OPENSSL_LIB) -I$(OPENSSL_INCLUDE) -I/opt/kremlin/kremlib -I$(HACL_HOME)/snapshots/hacl-c -I$(HACL_HOME)/snapshots/hacl-c-experimental

test-exp: test-exp.exe
	LD_LIBRARY_PATH=$(HACL_HOME)/build-experimental DYLD_LIBRARY_PATH=$(HACL_HOME)/build-experimental ./test-exp.exe

test-mult-c25519.exe:
	$(CC) $(CFLAGS) -c $(KREMLIN_HOME)/kremlib/testlib.c -o testlib.o -I$(KREMLIN_HOME)/kremlib
	$(CC) $(CFLAGS) -c $(KREMLIN_HOME)/kremlib/kremlib.c -o kremlib.o -I$(KREMLIN_HOME)/kremlib
	$(CC) $(CFLAGS) -c random.c -o random.o -I$(KREMLIN_HOME)/kremlib -I$(HACL_HOME)/snapshots/hacl-c-experimental
	$(CC) $(CFLAGS) -c Hacl_Impl_Bignum.c -o Hacl_Impl_Bignum.o -I$(KREMLIN_HOME)/kremlib -I$(HACL_HOME)/snapshots/hacl-c -I$(HACL_HOME)/snapshots/hacl-c-experimental
	$(CC) $(CFLAGS) -c $(HACL_HOME)/snapshots/hacl-c/Hacl_Curve25519.c -o Hacl_Curve25519.o -I$(KREMLIN_HOME)/kremlib -I$(HACL_HOME)/snapshots/hacl-c -I$(HACL_HOME)/snapshots/hacl-c-experimental
	$(CC) $(CFLAGS) -c test-mult.c -o test-mult.o  -I$(KREMLIN_HOME)/kremlib -I$(HACL_HOME)/snapshots/hacl-c -I$(HACL_HOME)/snapshots/hacl-c-experimental
	$(CC) $(CFLAGS) -o test-mult-c25519.exe random.o kremlib.o testlib.o Hacl_Impl_Bignum.o Hacl_Curve25519.o test-mult.o -I/opt/kremlin/kremlib -I$(HACL_HOME)/snapshots/hacl-c -I$(HACL_HOME)/snapshots/hacl-c-experimental -lcrypto

test-mult-c25519: test-mult-c25519.exe
	./test-mult-c25519.exe
build:
	$(MAKE) -C ../.. clean
	$(MAKE) -C ../.. build-experimental
	$(MAKE) clean
	$(MAKE) test-mult.exe

clean:
	rm -rf *~ *.exe *.o
