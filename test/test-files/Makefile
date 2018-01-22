OPENSSL_LIB=$(HACL_HOME)/other_providers/openssl
OPENSSL_INCLUDE=$(HACL_HOME)/other_providers/openssl/include

#CC=gcc-7 -pg -Ofast -flto
CC=gcc-7 -pg

test-rsapss.exe:
	$(CC) -c $(KREMLIN_HOME)/kremlib/testlib.c -o testlib.o -I$(KREMLIN_HOME)/kremlib
	$(CC) -c Hacl_Perf_RSA.c -o Hacl_Perf_RSA.o -L$(OPENSSL_LIB) -I$(OPENSSL_INCLUDE) -I$(KREMLIN_HOME)/kremlib -I$(HACL_HOME)/snapshots/hacl-c -I$(HACL_HOME)/snapshots/hacl-c-experimental
	$(CC) -o test-rsapss.exe  testlib.o Hacl_Perf_RSA.o -lhacl -lcrypto -L$(HACL_HOME)/build-experimental -L$(OPENSSL_LIB) -I$(OPENSSL_INCLUDE) -I/opt/kremlin/kremlib -I$(HACL_HOME)/snapshots/hacl-c -I$(HACL_HOME)/snapshots/hacl-c-experimental

test-unit-rsapss: test-rsapss.exe
	LD_LIBRARY_PATH=$(HACL_HOME)/build-experimental DYLD_LIBRARY_PATH=$(HACL_HOME)/build-experimental ./test-rsapss.exe unit-test

test-perf-rsapss: test-rsapss.exe
	LD_LIBRARY_PATH=$(HACL_HOME)/build-experimental DYLD_LIBRARY_PATH=$(HACL_HOME)/build-experimental ./test-rsapss.exe perf

clean:
	rm -rf *~ *.exe *.o
