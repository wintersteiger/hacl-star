OPENSSL_LIB=$(HACL_HOME)/other_providers/openssl
OPENSSL_INCLUDE=$(HACL_HOME)/other_providers/openssl/include

.PHONY=build

CC=gcc-7 -Ofast -flto
#CC=gcc-7 -pg
#CFLAGS=-Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops -flto

test-rsapss.exe:
	$(CC) $(CFLAGS) -c $(KREMLIN_HOME)/kremlib/testlib.c -o testlib.o -I$(KREMLIN_HOME)/kremlib
	$(CC) $(CFLAGS) -c Hacl_Perf_RSA.c -o Hacl_Perf_RSA.o -L$(OPENSSL_LIB) -I$(OPENSSL_INCLUDE) -I$(KREMLIN_HOME)/kremlib -I$(HACL_HOME)/snapshots/hacl-c -I$(HACL_HOME)/snapshots/hacl-c-experimental
	$(CC) $(CFLAGS) -o test-rsapss.exe  testlib.o Hacl_Perf_RSA.o -lhacl -lcrypto -L$(HACL_HOME)/build-experimental -L$(OPENSSL_LIB) -I$(OPENSSL_INCLUDE) -I/opt/kremlin/kremlib -I$(HACL_HOME)/snapshots/hacl-c -I$(HACL_HOME)/snapshots/hacl-c-experimental

test-unit-rsapss: test-rsapss.exe
	LD_LIBRARY_PATH=$(HACL_HOME)/build-experimental DYLD_LIBRARY_PATH=$(HACL_HOME)/build-experimental ./test-rsapss.exe unit-test

test-perf-rsapss: test-rsapss.exe
	LD_LIBRARY_PATH=$(HACL_HOME)/build-experimental DYLD_LIBRARY_PATH=$(HACL_HOME)/build-experimental ./test-rsapss.exe perf

test.exe:
	$(CC) $(CFLAGS) -c $(KREMLIN_HOME)/kremlib/testlib.c -o testlib.o -I$(KREMLIN_HOME)/kremlib
	$(CC) $(CFLAGS) -c Hacl_Mult.c -o Hacl_Mult.o -I$(KREMLIN_HOME)/kremlib
	$(CC) $(CFLAGS) -c Hacl_Perf_Mult.c -o Hacl_Perf_Mult.o  -I$(KREMLIN_HOME)/kremlib -I$(HACL_HOME)/snapshots/hacl-c -I$(HACL_HOME)/snapshots/hacl-c-experimental
	$(CC) $(CFLAGS) -o test.exe  testlib.o Hacl_Mult.o Hacl_Perf_Mult.o -lhacl -lcrypto -L$(HACL_HOME)/build-experimental -I/opt/kremlin/kremlib -I$(HACL_HOME)/snapshots/hacl-c -I$(HACL_HOME)/snapshots/hacl-c-experimental

test: test.exe
	LD_LIBRARY_PATH="../../build-experimental" DYLD_LIBRARY_PATH="../../build-experimental" ./test.exe


build:
	$(MAKE) -C ../.. clean
	$(MAKE) -C ../.. build-experimental
	$(MAKE) clean
	$(MAKE) test.exe

clean:
	rm -rf *~ *.exe *.o
