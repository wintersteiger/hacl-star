all:
	$(CC) -c /opt/kremlin/kremlib/testlib.c -o testlib.o -I/opt/kremlin/kremlib
	$(CC) -c Hacl_Perf_RSA.c -o Hacl_Perf_RSA.o -L/usr/local/Cellar/openssl@1.1/1.1.0g/lib -I/usr/local/Cellar/openssl@1.1/1.1.0g/include -I/opt/kremlin/kremlib -I/opt/hacl-star/snapshots/hacl-c -I/opt/hacl-star/snapshots/hacl-c-experimental
	$(CC) -o test.exe  testlib.o Hacl_Perf_RSA.o -lhacl -lcrypto -L. -L/usr/local/Cellar/openssl@1.1/1.1.0g/lib -I/usr/local/Cellar/openssl@1.1/1.1.0g/include -I/opt/kremlin/kremlib -I/opt/hacl-star/snapshots/hacl-c -I/opt/hacl-star/snapshots/hacl-c-experimental
	LD_LIBRARY_PATH=. DYLD_LIBRARY_PATH=. ./test.exe

clean:
	rm -rf *~ *.exe *.o
