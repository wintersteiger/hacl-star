#include <sys/types.h>
#include <sys/stat.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <assert.h>
#include <time.h>

#include "Crypto_HKDF_Crypto_HMAC_Crypto_Hash.h"

#include "quic_provider.h"

static void dump(char* info, unsigned char buffer[], size_t len)
{
  size_t i;
  printf("%12s[%3d] ", info, (int) len);
  for(i=0; i<len; i++) {
    printf("%02x",buffer[i] & 0xFF);
    if (i % 32 == 31 || i == len-1) printf("\n");
  };
  if (len == 0) printf("\n");
}

int main(int argc, char **argv)
{
  unsigned char hash[64] = {0};
  unsigned char input[] = "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu"; // 896 bits

  // TODO actually check the outputs

  size_t len = 0;
  dump("input",input, len);
  quic_crypto_hash(TLS_hash_SHA256, hash, input, len);
  dump("SHA256", hash, 32);
  Crypto_Hash_compute256(len, input, hash);
  dump("SHA256", hash, 32);
  Crypto_Hash_compute(Crypto_Hash_SHA256, len, input, hash);
  dump("SHA256", hash, 32);
  quic_crypto_hash(TLS_hash_SHA384, hash, input, len);
  dump("SHA384", hash, 48);
  quic_crypto_hash(TLS_hash_SHA512, hash, input, len);
  dump("SHA512", hash, 64);

  len = 3;
  dump("input",input, len);
  quic_crypto_hash(TLS_hash_SHA256, hash, input, len);
  dump("SHA256", hash, 32);
  Crypto_Hash_compute256(len, input, hash);
  dump("SHA256", hash, 32);
  Crypto_Hash_compute(Crypto_Hash_SHA256, len, input, hash);
  dump("SHA256", hash, 32);
  quic_crypto_hash(TLS_hash_SHA384, hash, input, len);
  dump("SHA384", hash, 48);
  quic_crypto_hash(TLS_hash_SHA512, hash, input, len);
  dump("SHA512", hash, 64);

  len = 896 / 8;
  dump("input",input, len);
  quic_crypto_hash(TLS_hash_SHA256, hash, input, len);
  dump("SHA256", hash, 32);
  Crypto_Hash_compute256(len, input, hash);
  dump("SHA256", hash, 32);
  Crypto_Hash_compute(Crypto_Hash_SHA256, len, input, hash);
  dump("SHA256", hash, 32);
  quic_crypto_hash(TLS_hash_SHA384, hash, input, len);
  dump("SHA384", hash, 48);
  quic_crypto_hash(TLS_hash_SHA512, hash, input, len);
  dump("SHA512", hash, 64);

  unsigned char key[] = "Jefe";
  unsigned char data[] = "what do ya want for nothing?";
  dump("key", key, 4);
  dump("data", data, 28);
  unsigned char text1[] = "\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x36\x77\x68\x61\x74\x20\x64\x6f\x20\x79\x61\x20\x77\x61\x6e\x74\x20\x66\x6f\x72\x20\x6e\x6f\x74\x68\x69\x6e\x67\x3f";
  for(int i = 0; i<4; i++) text1[i] ^= key[i];
  dump("text1", text1, 64 + 28);
  quic_crypto_hash(TLS_hash_SHA256, hash, text1, 64 + 28);
  dump("hash", hash, 32);
  unsigned char text2[] = "\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x5c\x93\x98\xc5\xb7\x8b\xb5\x68\x9f\x8a\x81\x2e\x00\xb9\xf7\xb9\x10\xd1\xfc\x17\xd9\xdb\xff\xba\x73\x94\xae\xfd\x4d\xc9\x9b\x37\x62";
  for(int i = 0; i<32; i++) text2[i+64] = hash[i];
  for(int i = 0; i<4; i++) text2[i] ^= key[i];
  dump("text2", text2, 64 + 32);
  quic_crypto_hash(TLS_hash_SHA256, hash, text2, 64 + 32);
  dump("hash", hash, 32);
  quic_crypto_hmac(TLS_hash_SHA256, hash, key, 4, data, 28);
  dump("HMAC-SHA256", hash, 32);

  assert(memcmp(hash, "\x5b\xdc\xc1\x46\xbf\x60\x75\x4e\x6a\x04\x24\x26\x08\x95\x75\xc7\x5a\x00\x3f\x08\x9d\x27\x39\x83\x9d\xec\x58\xb9\x64\xec\x38\x43", 32) == 0);

  quic_crypto_hmac(TLS_hash_SHA384, hash, key, 4, data, 28);
  dump("HMAC-SHA384", hash, 48);
  assert(memcmp(hash, "\xaf\x45\xd2\xe3\x76\x48\x40\x31\x61\x7f\x78\xd2\xb5\x8a\x6b\x1b\x9c\x7e\xf4\x64\xf5\xa0\x1b\x47\xe4\x2e\xc3\x73\x63\x22\x44\x5e\x8e\x22\x40\xca\x5e\x69\xe2\xc7\x8b\x32\x39\xec\xfa\xb2\x16\x49", 48) == 0);

  quic_crypto_hmac(TLS_hash_SHA512, hash, key, 4, data, 28);
  dump("HMAC-SHA512", hash, 64);
  assert(memcmp(hash, "\x16\x4b\x7a\x7b\xfc\xf8\x19\xe2\xe3\x95\xfb\xe7\x3b\x56\xe0\xa3\x87\xbd\x64\x22\x2e\x83\x1f\xd6\x10\x27\x0c\xd7\xea\x25\x05\x54\x97\x58\xbf\x75\xc0\x5a\x99\x4a\x6d\x03\x4f\x65\xf8\xf0\xe6\xfd\xca\xea\xb1\xa3\x4d\x4a\x6b\x4b\x63\x6e\x07\x0a\x38\xbc\xe7\x37", 64) == 0);

  unsigned char salt[] = "\x00\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0a\x0b\x0c";
  unsigned char ikm[] = "\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b\x0b";
  unsigned char info[] = "\xf0\xf1\xf2\xf3\xf4\xf5\xf6\xf7\xf8\xf9";

  printf("\nprk = HKDF-EXTRACT-SHA256('0x000102030405060708090a0b0c', '0x0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b')\n");
  quic_crypto_hkdf_extract(TLS_hash_SHA256, hash, salt, 13, ikm, 22);
  dump("", hash, 32);

  unsigned char prk[32] = {0};
  memcpy(prk, hash, 32);
  dump("", prk, 32);

  unsigned char okm[42] = {0};
  printf("\nokm = HKDF-EXPAND-SHA256(prk, '0xf0f1f2f3f4f5f6f7f8f9', 42)\n");
  if(!quic_crypto_hkdf_expand(TLS_hash_SHA256, okm, 42, prk, 32, info, 10))
  {
    printf("Failed to call HKDF-expand\n");
    return 1;
  }
  dump("", okm, 42);

  quic_secret s = { .hash = TLS_hash_SHA256, .ae = TLS_aead_AES_128_GCM };
  memcpy(s.secret, hash, 32);
  quic_crypto_tls_derive_secret(&s, &s, "EXPORTER-QUIC server 1-RTT Secret");

  quic_key* k;
  if(!quic_crypto_derive_key(&k, &s))
  {
    printf("Failed to derive key\n");
    return 1;
  }

  unsigned char cipher[128];
  printf("\nAES-128-GCM encrypt test:\n");
  quic_crypto_encrypt(k, cipher, 0, salt, 13, data, 28);
  dump("", cipher, 28+16);

  if(quic_crypto_decrypt(k, hash, 0, salt, 13, cipher, 28+16)) {
    printf("DECRYPT SUCCES: \n");
    dump("", hash, 28);
  } else {
    printf("DECRYPT FAILED.\n");
  }
  quic_crypto_free_key(k);

  s.hash = TLS_hash_SHA256;
  s.ae = TLS_aead_CHACHA20_POLY1305;

  if(!quic_crypto_derive_key(&k, &s))
  {
    printf("Failed to derive key\n");
    return 1;
  }

  printf("\nCHACHA20-POLY1305 encrypt test:\n");
  quic_crypto_encrypt(k, cipher, 0x29e255a7, salt, 13, data, 28);
  dump("", cipher, 28+16);

  if(quic_crypto_decrypt(k, hash, 0x29e255a7, salt, 13, cipher, 28+16)) {
    printf("DECRYPT SUCCES: \n");
    dump("", hash, 28);
  } else {
    printf("DECRYPT FAILED.\n");
  }

  quic_crypto_free_key(k);

  return 0;
}
